# The Lean corpus has ONE open obligation, and it is a statement about `y`

Companion to `DivisorTransformRecovery.md` sections 8-11. Nothing here is
progress on Erdos 257; it closes a lane and, more usefully, shows that three
apparently distinct lanes were always one.

## 1. Three sockets, one condition [PROVED, from source]

The cross-index lists 16 machine-checked theorems asserting
`Irrational (erdosSupportSeries ...)`. Three of them carry an explicitly OPEN
hypothesis -- the docstring at `CertificateKernel.lean:9213` says so outright:

> the analytic content is reduced to certificate existence for `f_A`, which for
> arbitrary infinite `A` remains an **OPEN obligation** -- this theorem does NOT
> resolve it.

Written out at `b = 2`, with `tau_A = supportCoeff A`, all three share conditions
(2), (3), (4) verbatim -- a bounded middle block, a continuing support, and
`q (C + N + L + 2) < 2^L` -- and differ only in the first block:

| socket | locus | first-block condition |
|---|---|---|
| **digitwise** | `CertificateKernel.lean:9219` | `forall r in [1,K], 2^r \| tau_A(N+r)` |
| **carried** | `CertificateKernel.lean:9569` | `2^K \| sum_{r=1..K} tau_A(N+r) 2^(K-r)` |
| **sunflower** | `SupportSunflowerDichotomy.lean:447` | *identical to the carried one* |

Two collapses, both readable in the source rather than conjectured:

* `SupportSunflowerDichotomy.lean:461` discharges the sunflower theorem by
  `exact irrational_erdosSupportSeries_of_weighted_coeff_carry_certificates`.
  So **sunflower = carried**, specialised to `supportCoeff A`; it is not a
  separate lane.
* `CertificateKernel.lean:9558` converts digitwise into carried by
  `carry_block_dvd_of_digitwise_blocks`. So **digitwise => carried**, and the
  implication is already formalised.

The digitwise implication is also immediate by hand: `2^r | tau_A(N+r)` makes each
`tau_A(N+r) 2^-r` an integer, so the truncation `sum_{r=1..K} tau_A(N+r) 2^-r` is
an integer, which is precisely the carried condition (see section 2). The
digitwise socket is therefore **strictly stronger**, and buys nothing.

> **The Lean corpus's entire remaining analytic obligation for arbitrary supports
> is a single condition.**

## 2. And that condition is about `y`, not about `A`

`DivisorTransformRecovery.md` section 11 proves, and verifies on 7787 `(N,K)`
pairs with 0 mismatches, that the carried first-block condition is exactly

    trunc_K(N) := sum_{r=1..K} tau_A(N+r) 2^-r   is an INTEGER,

since `sum_{r=1..K} tau_A(N+r) 2^(K-r) = 2^K * trunc_K(N)`. With
`R(M) = sum_{j>=1} tau_A(M+j) 2^-j` and `R(N) = trunc_K(N) + 2^-K R(N+K)`,
condition (4) forces the remainder below `1/q`, so the socket says

    R(N) = integer + eps,  0 <= eps < 1/q,   i.e.   {2^N y} < 1/q,

and therefore

> **socket  <=>  liminf_N {2^N y} = 0.**

Consequences, unchanged from section 11 and now applying to all three loci:

* it is a statement about `y`'s **numerical value**, the class
  `ProgrammeSpine.md` section 12 identifies as the shared defect of all six
  killed families;
* `socket => irrational` but `irrational =/=> socket` (an irrational whose binary
  expansion has no long zero runs has `liminf > 0`), so the hypothesis is
  **strictly stronger than the conclusion it yields**, and establishing it for a
  given `A` is harder than proving 257 for that `A`.

## 3. What is genuinely left

Of the 16 machine-checked criteria, the 13 that are unconditional cover only
already-settled families: `univ`, multiples of `d`, periodic, eventually
periodic, residue classes, odds, pairwise-coprime-and-summable, the
reciprocal-summable theorem, close-return (walled in sections 8-9), the bouquet
(subsumed -- `SupportSunflowerDichotomy.lean:210` proves every bouquet support is
reciprocal-summable), and two tail-transfer lemmas. The remaining three are the
one socket above.

**So the Lean corpus contains no open support-structural obligation at all.** Its
only open obligation is a numerical-value statement strictly stronger than the
theorem. Anyone planning to "supply the certificate" should read section 2 first.

**Nonclaim.** This does not bear on whether 257 is true. It says where the
formal corpus's remaining hypothesis actually lives, and that the three lanes a
reader would try next are one lane, already characterised.


## 4. Locus freshness (the sibling is editing this Lean file live)

Line numbers in `SupportSunflowerDichotomy.lean` MOVE. Verified against the file
as of this edit: `summable_reciprocalSupportTerm` at `:210`,
`irrational_erdosSupportSeries_of_orthogonalPetalBouquet_unconditional` at `:438`,
`SunflowerForcedCarrySupply` at `:447`, the sunflower theorem at `:458` with its
discharge into the carried socket at `:461`, and the conditional bouquet route at
`:617`. An earlier revision of this note cited `:381`/`:384`/`:540`; those are stale.
**Re-grep by symbol name, never trust a line number in this file.**

One substantive change came with the renumbering: the bouquet endpoint is now
**unconditional** (`:438`, "no selector hypothesis needed"), stronger than the
subsumption recorded in section 3, which went through the summability theorem and
a forced slot-tail selection. Section 3's conclusion is unaffected -- the bouquet
is closed either way -- but the unconditional form is the one to cite.
## 5. Death hunt on `3/(2^k - 1)`, k = 31..80 -- NOT a one-way result

Receipt: `state/formal_math/erdos257_period_noncollapse/mersenne3_death_hunt_receipt.json`

`erdos257_hole_geometry/notes/MersenneBlockRenormalization.md` section 4 sets two
one-way targets for that family; item 2 is "produce a certified late death,
eliminating that member". Their run covered `3 <= k <= 30` at 100000 certified
ranks and four branches near `k = 300`. I ran the **untested band** `k = 31..80`
on my independent enclosure engine (`scripts/late_hazard_profile.py::run_target`,
cross-checked earlier against an exact-`Fraction` greedy sharing no code with it),
depth 4000, `P = 12200` bits.

**Result: 50/50 alive; 0 dead, 0 terminated, 0 indeterminate.**

**This is not progress**, and it is recorded so the band is not re-searched.
A certified death would have been one-way; survival is not (T12 -- finite depth
never confirms survival). Support density sits at `0.47` across the band
(`|supp| ~ 1875..1900` of 4000), matching the known `rho -> 1/2` and adding
nothing. Depth here is far shallower in *block* terms than theirs: their block
scale is `k`, so 4000 ranks is only 50 blocks at `k = 80` against their 1000.

### One structural remark that is exact

Their section 2 argues the block scale `k` is "a genuine coefficient-extraction
cascade, not an arbitrarily chosen plotting scale". There is a one-line reason,
from the target's closed form:

    3/(2^k - 1) = 3 * sum_{j>=1} 2^(-jk) = sum_{j>=1} ( 2^(-(jk-1)) + 2^(-jk) ),

so **the binary expansion of `y_k` is periodic with period exactly `k`, carrying
exactly two 1s per period, at offsets `= 0` and `= -1 mod k`.** The block scale is
the target's own binary period. Two corollaries, both immediate:

* the longest zero-run in `y_k` is `k - 2` and it recurs, so
  `liminf_N {2^N y_k} > 0` -- the section 11 socket fails for `y_k`, as it must
  for any non-dyadic rational;
* summing the carry recursion `D_N = 2 D_{N-1} + t_N - tau_A(N)` gives
  `mean(tau_A) = mean(t) + mean(D)` with `mean(t) = 2/k` exactly, so if `y_k` had
  an infinite greedy support then `H_A(x) -> infinity` (forced by the sibling Lean
  theorem, since `y_k` is rational) and hence

      mean(D)(x) = H_A(x) - 2/k  ->  infinity,

  i.e. the mean carry must diverge against a *fixed* digit mean `2/k`.

Neither corollary is a contradiction; they are stated exactly so the next attempt
starts from the closed form rather than from a measured block scale.

## 6. `3/(2^k - 1)` can never terminate -- every member is a real candidate [PROVED + EXHAUSTIVE]

`erdos257_hole_geometry/notes/MersenneBlockRenormalization.md` opens its lane with
"can one prove that a member of `y_k = 3/(2^k - 1)` has an infinite greedy
support? One such proof would disprove Erdős 257." That framing needs the greedy
support to be **infinite**, not merely non-dying: a target whose greedy
*terminates* has a finite support and disproves nothing. The note does not rule
termination out. This section does.

### The decision procedure

`SupportWordStructureLab.md` section 4g proves, via Bang's primitive-prime
theorem, that a finite Mersenne sum `sum_{a in F} 1/(2^a - 1) = p/q` in lowest
terms has

    F  subset  {1, 2, 3, 6}  u  { d : d | ord_q(2) }.        (4g.1)

For `q = 2^k - 1` we have `ord_q(2) = k` exactly, so the candidate set is
`{1,2,3,6} u div(k)` -- always small enough to enumerate **completely**.

### Proved, for every Mersenne prime

Let `2^k - 1` be prime; then `k` is prime, so `div(k) = {1, k}` and
`F subset {1,2,3,6,k}`. For the reduced denominator to be exactly `2^k - 1`
(prime, and `> 63` once `k >= 7`, hence coprime to `63`) the `{1,2,3,6}` part
must sum to an **integer**. The subsets of `{1, 1/3, 1/7, 1/63}` that do are only
`{}` and `{1}` -- every other subset sum has denominator `3`, `7`, `21` or `63`
(e.g. `1/3 + 1/7 + 1/63 = 31/63`). Hence the only finite Mersenne sums with
denominator `2^k - 1` are

    1/(2^k - 1)      and      1 + 1/(2^k - 1) = 2^k/(2^k - 1),

i.e. `m in {1, 2^k}`. In particular **`m = 3` is not attainable**, so
`3/(2^k - 1)` has no finite representation.

### Verified exhaustively, `k = 3..40`

Complete enumeration over `F subset {1,2,3,6} u div(k)` (from 15 to 1023 subsets
per `k`), exact `Fraction` arithmetic, asking whether any subset sums to
`3/(2^k - 1)`: **no `k` in `3..40` admits one.** The prime rows reproduce the
proved pair exactly --

| `k` | `2^k - 1` prime | attainable `m` with denominator `2^k - 1` |
|---|---|---|
| 3, 5, 7, 13, 17, 19, 31 | yes | exactly `{1, 2^k}` |
| 6 | no | `1, 10, 22, 31, 64, 73, ...` |
| 8 | no | `1, 86, 103, 256, 341, 358` |
| 40 | no | `1, 1074791426, 1075840003, ...` |

-- and `3` appears in no row, prime or composite.

### Why, structurally

For `F subset div(k)`, `sum_{a in F} 1/(2^a - 1) = M_F/(2^k - 1)` with
`M_F = sum_a (2^k - 1)/(2^a - 1)`, and each `(2^k - 1)/(2^a - 1) = 1 + 2^a + ...`
is **odd**. So `M_F = 3` needs either three terms of value `1` -- but only `a = k`
gives `1`, so that is a multiset, banned by set-ness -- or a single term of value
`3`, i.e. `1 + 2^a = 3` with `k/a = 2`, forcing `k = 2`. The `{1,2,3,6}`
exceptions (where Bang's theorem fails) are what the enumeration above covers.

### Consequence for the construction lane

> For every `k >= 3` with `2^k - 1` prime, `3/(2^k - 1)` **cannot terminate**.
> Therefore if any such member is ever shown not to die, its support is
> automatically infinite and Erdős 257 is false.

That removes a disjunct their lane would otherwise have to close separately:
survival alone suffices for those members, and the family is a genuine candidate
family rather than a possibly-terminating one. It does **not** say any member
survives -- section 5's hunt found no death and no termination, and survival is
not certifiable at finite depth (T12).

## 7. The exhaustion map's SOLVED/OPEN split omits a third solved class [CROSS-SETTLEMENT]

`docs/formal_math/erdos257_computational_exhaustion_map_2026_08_22.md` section AO
states the map after ten iterations:

    SOLVED  (i)  A eventually periodic          -> Lambert over APs; N is period 1
            (ii) A base-adapted, Y_A Mahler     -> Nishioka
    OPEN         everything else                -> Erdos 257

and concludes "A counterexample must be **aperiodic** and **not base-adapted for
any `k`**. Those are now the only two escape routes."

**There is a third solved class, and it is machine-checked in the sibling
directory.** `ReciprocalSupportIrrationality.lean:1013` (chain `sorry = 0`,
`axiom = 0`):

    theorem irrational_erdosSupportSeries_two_of_summable_reciprocal
        (A : Set N) (hA : A.Infinite)
        (hsum : Summable (reciprocalSupportTerm A)) :
        Irrational (erdosSupportSeries 2 A)

Every reciprocal-summable infinite support is solved. Summability is neither
periodicity nor base-adaptation, so class (iii) is not contained in (i) or (ii).

### A witness, taken from section AN's own table

Section AN measures base-adaptation by Mahler nullity at `(d=2, D=5)` and records

| sequence | k=2 | k=3 | k=4 |
|---|---|---|---|
| `2^{2^k}` | 0 | 0 | 0 |

concluding that `2^{2^k}` "fires at **no** base -- doubly-exponential growth is
not adapted to any fixed multiplication-by-`k`". Take `A = {2^(2^k)}`. Then

* **not base-adapted** -- by section AN's own measurement;
* **aperiodic** -- `|A ∩ [1,N]| ~ log log N`, so density `0`; an eventually
  periodic set has positive density;
* **reciprocal-summable** -- `1/2 + 1/4 + 1/16 + 1/256 + ... ` converges
  superexponentially.

So section AO's map places `A` in **OPEN**, while the theorem above proves
`sum_k 1/(2^(2^k) - 1)` is **irrational**. The witness section AN chose to
demonstrate the narrowness of the Nishioka class is itself an instance of the
class section AO omits.

### The corrected split, and the sharper profile

    SOLVED  (i)   A eventually periodic
            (ii)  A base-adapted, Y_A Mahler
            (iii) A reciprocal-summable            [machine-checked, sibling dir]
    OPEN          everything else

> **A counterexample must be aperiodic, not base-adapted for any `k`, AND
> harmonically divergent (`sum_{a in A} 1/a = infinity`).**

Three escape routes closed, not two. The third is the one that bites hardest on
the construction lane: it forces any candidate support to be *dense enough* that
its reciprocals diverge, which is precisely the regime where close-return is
walled (sections 8-9 of `DivisorTransformRecovery.md`) and where the measured
`rho -> 1/2` sits.

**Nonclaim.** Constraint (iii) is a theorem; the density figure `rho ~ 0.47-0.50`
is *measured*, not proved, and is not part of the profile. Nothing here says a
counterexample exists.

## 8. Independent Mahler detector: one control row of section AN is wrong

Script: `scripts/mahler_nullity_independent.py` (exact rational linear algebra, no
code shared with the sibling's detector).

Exhaustion-map section AN measures base-adaptation as the nullity of
`sum_{i=0..d} p_i(x) Y(x^(k^i)) = q(x)` at `(d=2, D=5)`, and argues the detector
is sound because its rows are "exactly what Mahler theory predicts". Section 7
above leans on one of those rows (`2^(2^k)` firing nowhere), so the detector was
worth reimplementing.

### Rows confirmed, and one that is not

| sequence | mine (k=2,3,4) | section AN | verdict |
|---|---|---|---|
| Thue-Morse (their control) | **5, 0, 0** | **5, 0, 0** | exact match |
| `2^(2^k)` | 0, 0, 0 | 0, 0, 0 | match -- **section 7's witness is independently confirmed** |
| primes | 0, 0, 0 | 0, 0, 0 | match |
| powers of 2 | 12, 0, 10 | 8, 0, 2 | same zero/nonzero pattern; magnitudes differ with `deg q` and window |
| powers of 3 | 0, 12, 0 | 0, 3, 0 | same pattern, magnitudes differ |
| **N (all naturals)** | **14, 9, 8** | **0, 0, 0** | **disagreement** |

`N` must fire, and the witness is one line: `Y_N(x) = sum_{n>=1} x^n = x/(1-x)` is
**rational**, so

    (1 - x) * Y(x)  +  0 * Y(x^k)  +  0 * Y(x^(k^2))  =  x

is an exact solution with `deg p_0 = 1 <= D` and `deg q = 1 <= D`. Nullity is
therefore positive at every `k`, and `0` cannot be right for the equation as
section AN states it.

**Does it damage their conclusions?** Not the map: section AO already places `N`
in class (i) (eventually periodic, period 1), so `N` also being base-adapted is
harmless. What it damages is the *soundness argument* -- section AN cites its rows
as proof the detector is wired, and one cited row is wrong. Anyone relying on a
section AN zero should re-derive it; the `2^(2^k)` zero that section 7 uses is now
independently confirmed above and does not need that.

### The realised-support check: consistent, and a lesson about windows

If `y` is rational with greedy support `A`, then `A` cannot be base-adapted --
otherwise Nishioka makes the sum irrational. So realised supports must show
nullity `0`. Measured on certified greedy prefixes (depth 380):

| target | k=2 | k=3 | k=4 at M=160 | M=240 | M=320 | M=390 |
|---|---|---|---|---|---|---|
| `1/21` | 0 | 0 | 0 | 0 | 0 | 0 |
| `4/9` | 0 | 0 | 0 | -- | -- | -- |
| `3/(2^7 - 1)` | 0 | 0 | 0 | -- | -- | -- |
| `3/(2^13 - 1)` | 0 | 0 | **6** | **0** | 0 | 0 |
| `1/1009` | 0 | 0 | **5** | **0** | 0 | 0 |

The two nonzero entries at `M = 160` are **window artifacts**: a relation can hold
across a short prefix without holding on the sequence, and both collapse to `0` as
soon as more coefficient equations are imposed. The control discriminates exactly
as it should -- Thue-Morse stays at `5` for every `M` in `160..390`, because its
relation is genuine.

**Verdict: consistent, no inconsistency found.** That was the expected outcome and
it is not progress on 257. The transferable part is the method: a nullity verdict
on a finite prefix is meaningless until it is shown stable under a growing
equation window, and the sibling's own Thue-Morse row is the right control for
that.

## 9. Section AI reproduces exactly -- and that calibrates section 8

Section 8 found one exhaustion-map control row wrong. Before treating that as a
reason to distrust the map's measurements generally, the most load-bearing of
them was re-derived independently. It holds, to the digit.

Exhaustion-map section AI claims the divisor transform erases complexity: a
minimum-complexity input (Sturmian, subword complexity `k+1`) and a
maximum-complexity input (random, `2^k`) yield `tau_A` of the *same* complexity
at matched density. Reimplemented with no shared code, `N = 6000`, exact counts
of distinct length-`k` windows:

| support | density | input `p(1..5)` | output `tau_A` `p(1..5)` | section AI |
|---|---|---|---|---|
| Sturmian `1/phi` | 0.618 | 2, 3, 4, 5, 6 | **36, 353, 2003, 4828, 5843** | identical |
| Sturmian `sqrt2 - 1` | 0.414 | 2, 3, 4, 5, 6 | **28, 216, 1157, 3435, 5321** | identical |
| Sturmian `1/sqrt2` | 0.707 | 2, 3, 4, 5, 6 | **40, 418, 2369, 5138, 5880** | identical |
| random matched | 0.619 | 2, 4, 8, 16, 32 | 34, 329, 1889, 4756, 5833 | 35, 322, 1852, 4713, 5832 |
| random matched | 0.411 | 2, 4, 8, 16, 32 | 24, 199, 1086, 3401, 5330 | 26, 200, 1068, 3317, 5369 |
| random matched | 0.714 | 2, 4, 8, 16, 32 | 39, 411, 2358, 5150, 5906 | 40, 463, 2748, 5410, 5919 |

All three **deterministic** rows match exactly; the random rows differ only by
seed and agree in magnitude. The input columns read exactly `k+1` and `2^k`, so
both instruments are measuring what they claim.

### Why this matters more than the confirmation itself

> Section AN's `N` row is an **isolated defect, not a systemic one.**

Section 8 could be read as grounds for distrusting the exhaustion map's numbers.
It is not. The map's most-cited measurement reproduces perfectly under an
independent implementation, so the correct response to section 8 is to fix that
one row, not to discount section AJ/AM's law -- which rests on section AI and is
therefore on solid measured ground.

**Nonclaim.** A confirmation is not progress on 257. Its value is calibration:
it tells the next actor which measured claims can be leaned on and which need
re-derivation.

## 10. ProgrammeSpine section 19 reproduces exactly too

Second load-bearing measured claim re-derived independently. Section 19 closes the
divisor-indexed null for the realised greedy support of `1/21` at 20000 ranks,
using

    SHARING(k) = sum_{i<=k} (mu_i - 1),   mu_i = max_{j<i} gcd(a_i, a_j)
    DEFECT(k)  = sum_{i<=k} (a_i - phi(a_i))

Recomputed with my own certified enclosure engine and my own statistic code
(no shared implementation):

| quantity | section 19 | independent |
|---|---|---|
| support size | 10006 | **10006** |
| density | 0.5003 | **0.5003** |
| SHARING per element | 2418.570 | **2418.570** |
| DEFECT per element | 3909.292 | **3909.292** |

Exact agreement to three decimals on both statistics, and an exact match on the
support size -- which also cross-validates their greedy engine against mine at
20000 ranks, since a single divergent take/skip would move `|supp|`.

**Controls, now completed.** The raw statistics match exactly, including their
structured power control; only the *random* control calibration differs.

| quantity | section 19 | independent |
|---|---|---|
| realised SHARING / DEFECT | 2418.570 / 3909.292 | **2418.570 / 3909.292** |
| evens control SHARING / DEFECT | 3300.40 / 5947.84 | **3300.403 / 5947.836** |
| random control SHARING | 2425.998 +/- 12.815 | 2442.729 +/- 17.928 |
| random control DEFECT | 3923.124 +/- 22.131 | 3923.830 +/- 20.680 |
| z(SHARING) / z(DEFECT) | -0.58 / -0.63 | -1.35 / -0.70 |
| evens z(SHARING) / z(DEFECT) | ~ +68 / +91 | +47.8 / +97.9 |

The `z` values are **control-construction dependent**: my controls draw each
element independently with probability `dens`, giving a binomially varying size,
whereas a fixed-size control would shift the SHARING mean and tighten its spread.
The DEFECT means agree to within 0.02%; the SHARING means differ by 16.7, about
one of my standard deviations.

**The verdict is unchanged and is what matters.** Both realised `z` scores sit far
inside section 19's own stated threshold -- it says "Eight seeds give a coarse
standard deviation; `|z|` below about 3 here means 'no deviation detected at this
sample size'" -- and the power control fires enormously under either calibration.
So the divisor-indexed null closes independently, with a test that independently
demonstrates its power. The exact `z` figures should not be quoted as constants.

### Running verification tally

| claim | status |
|---|---|
| exhaustion map section AI (complexity erasure) | **exact match**, all three deterministic rows (section 9) |
| ProgrammeSpine section 19 (realised SHARING/DEFECT) | **exact match**, both statistics |
| exhaustion map section AN, Thue-Morse / `2^(2^k)` / primes rows | **match** (section 8) |
| exhaustion map section AN, `N` row | **WRONG** -- `Y_N = x/(1-x)` is rational so nullity > 0 (section 8) |

One defect in four checks, and it is the one row whose correct value is
derivable in a single line. The corpus's measurements are otherwise reliable.

## 11. GapAvoidance section 3 confirmed -- with a precision caveat

Script: `scripts/gap_equidistribution_independent.py` (my certified enclosure
engine, no code shared with theirs).

The most load-bearing measured claim in the corpus. `GapAvoidance...md` section 3
normalises the skip position `v_n = rho_{n-1}/w_n` in `[0,1)` (fatal iff
`v_n > 1 - G_n/w_n`) and reports `P(v > 1-eps)/eps` at `eps = 2^-2 .. 2^-12`,
pooled over skips at rank `>= 40`. Its conclusion -- "there is no congruence,
height, phase, density, ownership, window, or carry signal distinguishing safe
from fatal orbits, because there is no signal" -- is cited as the structural
explanation for why all ~25 mechanism families died.

Re-derived, 1500 random targets per range, depth 250, rank `>= 40`, ~100k
certified skips per range (indeterminates stop the orbit, never resolved):

| range | skips | `2^-2` | `2^-4` | `2^-6` | `2^-8` | `2^-10` | `2^-11` | `2^-12` |
|---|---|---|---|---|---|---|---|---|
| `q 3..200` | 92890 | 0.98 | 0.93 | 0.89 | 0.87 | 0.86 | 0.77 | **0.71** |
| `q 1e5..2e5` | 101114 | 1.00 | 0.98 | 0.99 | 0.99 | 0.94 | 0.89 | **0.73** |
| `q 1e12..2e12` | 100091 | 1.01 | 1.00 | 0.99 | 0.99 | 1.01 | 0.96 | **1.15** |

*Instrument validated on their own control first:* the small-`q` range reproduces
the downward drift (mine `0.98 -> 0.71`, theirs `0.94 -> 0.79`), i.e. biased
**away** from danger, before any large-`q` verdict was read.

**Verdict: section 3 is confirmed.** The small-`q` repulsion is a transient, and
at `q ~ 10^12` the skip position is flat at `1.00` across nine decades of `eps`.

### The caveat: the finest bins are Poisson noise, not precision

Section 3 says the position is "equidistributed to measured precision `2^-12`".
That overstates what the finest bins can carry. At `eps = 2^-12` with ~100k
skips the expected count is `100091 / 4096 ~ 24`, so the Poisson relative
standard deviation is `~20%`. My `0.73` and `1.15` and their `1.16` are all
within about `2 sigma` of `1` and of each other. With their ~2.9e5 skips the
expected count is `~71`, still `~12%` -- their `1.16` sits `~1.3 sigma` out.

> The equidistribution holds; the `2^-12` bin is not evidence of anything, in
> either run. Quote the flatness through `2^-10`, not the last two bins.

This is the same species of caveat as section 10's `z` values: the conclusion
survives independent re-derivation, a quoted decimal does not.

### Verification programme complete

| claim | status |
|---|---|
| exhaustion map section AI (complexity erasure) | **exact** (section 9) |
| ProgrammeSpine section 19 (realised SHARING/DEFECT, evens control) | **exact**; `z` control-dependent (section 10) |
| section AN Thue-Morse / `2^(2^k)` / primes | **match** (section 8) |
| section AN `N` row | **WRONG**, one-line fix (section 8) |
| GapAvoidance section 3 (no local signal) | **confirmed**; finest bins noise (this section) |

Five load-bearing claims checked: four confirmed, one defect, two quoted-decimal
caveats. **The corpus's conclusions are sound.** None of this is progress on 257.

## 12. The constant 1 is ONE identity in four dresses, not three coincidences

`ProgrammeSpine.md` CORRECTION 2 observes that "the same constant 1 appears
**three independent times**: in their theorem, in `measure(Acal) = lim T_n = 1`,
and in the survival probability `1/E`", and treats the resulting critical balance
at `t = 2` as a striking coincidence. A fourth appearance sits in
`MobiusSignSupportNoGo.lean` as `tsum_mobiusOneTerm : sum' d, mobiusOneTerm d = 1`.

**They are not independent.** All four are the single geometric identity

    sum_{j >= 1} t^-j  =  1/(t - 1),        at t = 2 both sides equal 1,

which at `t = 2` is the statement `2 - 1 = 1`.

| appearance | what it actually is |
|---|---|
| Kovac-Tao threshold `sum_k 1/(t_k - 1)` at `t = 2` | `1/(2 - 1)` -- the **right** side |
| `measure(Acal) = lim 2^N T_N = sum_{j>=1} 2^-j` | the **left** side of the same identity |
| survival probability `1/E` | its numerator is `measure(Acal)`, i.e. the row above |
| `tsum_mobiusOneTerm` | `mersenneWeight 1 = 1/(2^1 - 1) = 1/(2 - 1)` -- **the same expression** as row 1 |

Verified from source: `mersenneWeight n = 1 / ((2 : R)^n - 1)`
(`GreedyAchievementSet.lean`, `def mersenneWeight`), and `mobiusOneTerm d` is
`mersenneWeight d` at `d = 1` and `0` otherwise
(`MobiusSignSupportNoGo.lean`, `def mobiusOneTerm`), so the `= 1` theorem is the
single `d = 1` term and nothing more. Rows 1 and 4 are literally the same
expression `1/(2-1)`; row 2 is the series that sums to it; row 3 inherits from
row 2.

### Why this is worth recording

It converts a coincidence into an explanation. The corpus repeatedly notes that
`t = 2` is "critically balanced" and that the counterexample construction fails
there "by a vanishing margin". The reason is not that three unrelated constants
happen to agree:

> **Base 2 is exactly the base where the geometric tail equals one coin**, because
> `2 - 1 = 1`. Every appearance of the constant is that one fact.

That also says immediately why the margin `gamma_n = z_n - T_n ~ (2/3) 4^-n` is
positive but second-order: at `t = 2` the first-order terms cancel identically,
by the identity above, leaving only the `4^-n` correction. It is the same reason
`ProgrammeSpine` section 16 finds the `+-1` families differ only in the sign of
the `4^-n` term with the `a = 0` case sitting at `0`.

**Nonclaim.** This is an explanation, not a mechanism. It does not make 257
easier; it says the "coincidence" that has been driving the corpus's sense of
criticality is a single elementary identity, so no leverage should be expected
from the coincidence itself.

## 13. `coin_n > tail_n` is alphabet-generic; the Lambert structure is the discriminator

`ProgrammeSpine.md` section 30 reduces the corpus: "**The entire load-bearing
content of this corpus is the single inequality `coin_n > tail_n`.** K1 and the
covering kill are that inequality wearing two hats."

**This is not an attack on that claim.** Section 30 says nothing in the corpus
survives both screens except the inequality; it does not claim the inequality is
*sufficient* -- if it were, 257 would be closed. What follows is a refinement:
the inequality is **shared with alphabets in which the 257-analogue is false**,
so it cannot be the discriminating ingredient, and the ingredient that *is*
discriminating can be named exactly.

### Two superincreasing alphabets, opposite verdicts on the same support

| alphabet | superincreasing? | support = the evens | verdict |
|---|---|---|---|
| geometric `c_n = 3^-n` | **yes**: `sum_{k>n} 3^-k = (1/2) 3^-n < 3^-n` | `sum_{m>=1} 3^(-2m) = 1/8` | **RATIONAL**, infinite support |
| Mersenne `c_d = 1/(2^d - 1)` | **yes**: `1/31 = 0.0322 > tail_5 = 0.0316` | `sum_{k>=1} 1/(4^k - 1) = 0.42109768...` | **IRRATIONAL** |

The second is machine-checked -- `CertificateKernel.lean`,
`irrational_erdosSupportSeries_periodic`: a periodic support forces irrationality.
The first is a two-line geometric series.

So `coin_n > tail_n` holds in both, and the same periodic support is a
rationality **producer** in one alphabet and an irrationality **producer** in the
other. The inequality is therefore alphabet-generic and carries none of the
discriminating content.

### What the discriminator is

For a geometric alphabet `c_n = r^n` with rational `r`, a support that is a union
of arithmetic progressions sums to a **rational function of `r`**, hence rational.
For the Mersenne alphabet, `1/(b^d - 1) = sum_{j>=1} b^(-jd)`, so a support that is
a union of APs gives a **Lambert series over those APs**, which the exhaustion
map's section AO(i) records as the solved-by-irrationality case.

> The extra ingredient beyond superincreasingness is the **Lambert / divisor
> structure** -- exactly the thing that turns `1_A` into `tau_A = 1 * 1_A`. It is
> what flips periodicity from producing rationals to producing irrationals.

### Consequence

Any argument that uses only `coin_n > tail_n` proves nothing, because it applies
verbatim to `c_n = 3^-n` where the analogue is false. This is the same shape as
section 16's `+1` falsifier but stronger in one respect: the `+1` family escapes
by making the inequality **fail** (`tail_n` exceeds `coin_n` by `2/3 4^-n`),
whereas `3^-n` **satisfies** it and still admits a rational infinite subsum. So
the falsifier applies to arguments the `+1` test would pass.

**Nonclaim.** This does not contradict section 30, does not make 257 easier, and
is not a mechanism. It is a screen: it says where the discriminating content
cannot be, and names where it is.

## 14. The solved cases prove something STRICTLY STRONGER than 257 -- which is why they do not extend

Section 13 localised the discriminating content in the Lambert/divisor structure
and pointed at the machine-checked periodic case. Reading that proof settles what
the discriminator actually is, and the answer is not what section 13 guessed.

### The periodic case is not an analytic import

`irrational_erdosSupportSeries_periodic` does **not** invoke a classical
Lambert-over-AP irrationality theorem. Its entire proof is

    irrational_erdosSupportSeries_of_weighted_coeff_certificates b A hb
      (exists_weighted_coeff_certificates_supportCoeff_periodic b m A hb hm hper hpos)

i.e. it discharges **socket A** -- one of the three sockets section 1 showed are a
single condition. The constructor is explicit, not abstract: with `B = b * phi(m)`
it sets

    K = 9 * (q + B + m + 100),   kappa = ...,   E = ...,   L = 2^kappa

and its docstring names the three ingredients: "divisor-orbit divisibility for the
first block, the full-support divisor-pair average dominates the middle window
through `supportCoeff <= tau`, and the forward orbit of any positive support
element keeps the far tail alive."

So the *period* `m` enters through `phi(m)`, and that is the handle used to force
`b^r | tau_A(N+r)` on the first block.

### The consequence, and it is the point

Section 1 proved digitwise `=>` carried (via `carry_block_dvd_of_digitwise_blocks`),
and section 11 of `DivisorTransformRecovery.md` proved carried `<=>`
`liminf_N {2^N y} = 0`. Chaining:

> **For every periodic support, the machine-checked proof establishes
> `liminf_N {2^N y} = 0`** -- a statement about the binary expansion of `y`,
> strictly stronger than the irrationality it is used to derive.

That is why the route works there and cannot extend. It is not that a step "fails"
for general `A`; it is that the periodic construction proves a **stronger**
statement, one that for a general infinite support may simply be **false** -- an
irrational whose binary expansion has no long zero runs has `liminf > 0`. So:

* the solved classes are not partial progress toward 257; they are proofs of a
  different, stronger statement that happens to hold on those classes;
* generalising the certificate is not "filling a gap" -- it would require proving
  `liminf_N {2^N y} = 0` for every infinite `A`, which is strictly harder than 257
  and is not implied by it.

### Correction to section 13

Section 13 said the discriminator is "the Lambert/divisor structure". Sharper: the
Lambert structure is what makes the certificate **constructible** when a period is
available, via `phi(m)`. Absent a period there is no such handle -- not because the
divisor structure is missing, but because the construction is driven by the period,
not by the alphabet. The alphabet contrast in section 13 stands as a screen; its
explanatory clause is superseded by this section.

**Nonclaim.** No new bound on 257. What is established is where the solved cases'
power comes from and why it is not extensible -- which retires "generalise the
certificate" as a lane.

## 15. Convergence: sections 12-13 and ProgrammeSpine section 31 are one phenomenon

`ProgrammeSpine.md` section 31 (commit `9b22394`) sharpens section 30. FACT 1
`coin_n > tail_n` has a two-step proof and only step 2 carries content:

    step 1  tail_n < 2 coin_{n+1}   (geometric domination -- OUR family's argument)
    step 2  2 coin_{n+1} < coin_n   <=>  2(2^n - 1) < 2^{n+1} - 1
                                    <=>  2^{n+1} - 2 < 2^{n+1} - 1

**an integer difference of exactly 1**, and across `x_d = 1/(2^d - a)` the three
families are the three values `+1, 0, -1`. Re-derived here independently:

| family | step-2 difference at `n = 1, 3, 7, 20` |
|---|---|
| `a = 1` (ours) | `+1 +1 +1 +1` -- gap, unique representations, 257 open |
| `a = 0` (`1/2^d`) | `0 0 0 0` -- exact tie |
| `a = -1` | `-1 -1 -1 -1` -- overlap, analogue FALSE (witness `1/7`) |

### How this relates to sections 12 and 13

**Independent, not duplicated.** Section 12 (`5f75c2c`) predates section 31
(`9b22394`) in commit order, and the two reach the same trichotomy by different
routes: section 12 through the identity `sum_j t^-j = 1/(t-1)` at `t = 2` and the
margin coefficient `(b-2)/(b-1)` vanishing iff `b = 2`; section 31 through the
integer arithmetic of step 2. Section 12 explains the *analytic* consequence (why
`gamma_n` is second-order); section 31 gives the *screening* form.

**Section 31's screen is sharper than section 13's, and section 13's witness does
not defeat it.** Section 13 showed `coin_n > tail_n` is alphabet-generic, with
`c_n = 3^-n` satisfying it while admitting the rational infinite subsum
`sum_m 3^(-2m) = 1/8`. But for that alphabet the step-2 comparison is
`2 * 3^n` vs `3^(n+1)`, a difference of `3^n` -- **not 1** -- so an argument that
consumes "the difference is exactly 1" does not run there. The two screens are
therefore complementary:

* section 13 catches arguments using only the *inequality* (they run at `3^-n`);
* section 31 catches arguments not using the *integer difference* (they run at
  `a = -1`).

Section 31 is the better default screen, being cheaper and identifying what the
bare inequality was missing. Section 13's contribution is the concrete witness
that the bare inequality really is insufficient -- which section 31 asserts but
does not exhibit.

### Also absorbed

`ProgrammeSpine.md` section 28 (`b7a8c1f3`) cross-validates the third agent's
deficit series `eps_k = sum_{j>=2} ((2^j-2)^2/(2^j-1)) z^j` and notes its
coefficient is zero at `j = 1` (`1 - 3 + 2`). That is the same `j = 1` vanishing
section 12 identifies for `gamma_n`, whose coefficient `(2^j - 2)/(2^j - 1)` is
zero for the same reason -- theirs is the square of the relevant factor. One root
cause, `2^1 = 2`, in three places.

**Nonclaim.** Nothing new about 257. This records that three separately-derived
results are one phenomenon and says which form to use for screening.

## 16. Applying their control lesson to my own section 11 -- a q-ladder with power

`ProgrammeSpine.md` section 31a records a methodological failure worth importing:

> My control set was drawn from the same hand-picked list the original lane used,
> and it reproduced the original selection effect rather than testing it. **A
> control that shares the selection bias of the thing it controls is not a
> control.** ... before reporting that a property is special to a class, exhibit a
> control set that would have *detected* the property elsewhere if it were common.

Audited against my own controls:

* **Section 10** (their section 19): my controls were freshly drawn
  density-matched independent sets, not a hand-picked list, so no selection bias.
  The caveat there was construction *sensitivity* (binomially-varying size shifts
  the `z`), a different failure mode. Stands.
* **Section 11** (their GapAvoidance section 3): **this one inherited their
  selection.** I tested exactly the three `q` ranges section 3 chose to
  demonstrate the transient. Reproducing an effect on the ranges picked to display
  it is not a control.

### The ladder

Statistic `P(v > 1-eps)/eps` at `eps = 2^-8` (chosen so the expected count is
`~305` per cell, not the `~24` of the `2^-12` bin that section 11 already flagged
as noise), ~78k certified skips per cell, 1200 random targets each:

| `q` magnitude | skips | ratio |
|---|---|---|
| `1e1` | 74438 | **0.874** |
| `1e2` | 80606 | **0.880** |
| `1e3` | 77753 | 1.057 |
| `1e4` | 77539 | 0.971 |
| `1e6` | 76973 | 1.154 |
| `1e8` | 81962 | 0.990 |
| `1e10` | 82312 | 0.942 |
| `1e12` | 79539 | 1.007 |

Poisson noise at this cell size is `1/sqrt(305) ~ 5.7%`, i.e. `+-0.057` at one
sigma. So the two small-`q` cells sit `~2 sigma` below 1 and agree with each
other, while every cell from `1e3` on lies within `~2 sigma` of 1 with no trend.

> **Section 3's transient is confirmed by a control that has power**: the ladder
> detected the repulsion where it exists and would have exposed a persistent or
> non-monotone bias at large `q` had one been there. This is no longer a
> reproduction on their chosen ranges.

*My own threshold error, recorded.* The script printed
`monotone non-decreasing (tolerance 0.03): False`. That verdict is wrong -- `0.03`
is tighter than the `0.057` noise, so it flags scatter as structure. Same error
class as section 11's `2^-12` bins and section 10's `z` values: **a decimal
threshold set without reference to the error bar.** Third instance this session;
the rule is to compute the noise before choosing the tolerance, not after.

**Nonclaim.** A confirmation, not progress. Its value is that section 11's
verification no longer inherits the selection it was meant to test.

## 17. M4 is not OPEN -- the only exhibitable class is machine-checked closed

`SurvivorMechanismCensus.md` (commit `62c6adc`) ranks the surviving mechanisms.
Its M4 row reads:

> **M4 -- Eventually-periodic supports: the only class in which a counterexample
> could ever be *exhibited* -- OPEN, and the probe says maximally generic**
>
> *Why it is the right class.* `K13` makes enumeration circular and `K1` forbids
> numerical certificates, so a counterexample can only ever be produced by an
> **exact identity**, and exact identities need a rule-given support.
> Eventually-periodic supports are the first such class...
>
> *What it would have to prove/refute.* That no nonempty subset of `{L_a}`,
> `L_a = sum_{j >= 0} 1/(2^{a + jP} - 1)`, is rational.

**That statement is already proved**, in the sibling directory,
`CertificateKernel.lean` (`sorry = 0`, `axiom = 0`):

    theorem irrational_erdosSupportSeries_eventuallyPeriodic
        (b m N₀ : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hm : 0 < m)
        (hper : ∀ n : ℕ, N₀ ≤ n → (n + m ∈ A ↔ n ∈ A))
        (hinf : A.Infinite) :
        Irrational (erdosSupportSeries b A)

A nonempty union of residue classes mod `P`, with or without a finite
modification, is infinite and eventually `P`-periodic. So every one of the **2036
supports** M4's probe swept is provably irrational, and so is every other member
of the class, for every `P` -- not just `P <= 10`.

### What this changes

M4 is not open. And because M4 is billed as *the only class in which a
counterexample could ever be exhibited* -- the census's own argument being that
`K13` makes enumeration circular, `K1` forbids numerical certificates, so only an
exact identity can produce one, and exact identities need a rule-given support --
the consequence is sharper than closing one row:

> **The only class in which a counterexample could be exhibited is
> machine-checked counterexample-free.**

Any counterexample therefore has no eventually-periodic description. Combined with
section 7's profile, a counterexample must be aperiodic, not base-adapted, and
harmonically divergent -- and now also *not exhibitable by the census's own
criterion for exhibitability*.

### On the probe

M4's numerical work is not wasted and its result is exactly right: the
simplest-denominator rational inside a `2^4096` enclosure is `2^2035.4`, "which is
what a *generic* real returns". That is an independent confirmation of a proved
theorem, and a good one -- it would have caught an error in the Lean statement had
there been one. What is wrong is only the verdict line, and the cause is the
recurring one: `CertificateKernel.lean` is in the sibling directory, and the
census did not cross-check it. That is trap T13b (grep the other programme) in its
Lean form.

**Nonclaim.** No new bound on 257, and no criticism of the probe. This closes one
census row and, through the census's own exhibitability argument, removes the
constructive route.

## 18. M8: its "generic" verdict is predicted; only the forcing half is untouched

With M4 closed (section 17), `SurvivorMechanismCensus.md` has one entry left:

> **M8 -- The carry-vs-divisor-ceiling -- the only mechanism passing both screens;
> probe says generic**
>
> *The idea.* Everything in this corpus that leans on positivity uses a **lower**
> bound, and lower bounds survive doubling. Set-ness is an **upper** bound and
> nothing had used it. Since `y < 1 = coin_1`, `1` is never in `A`, so
> `tau_A(n) <= d(n) - 1` at every rank. ... Whenever `d(n) - 1 < 2 Q_{n-1} + t_n`
> the carry is **forced strictly upward**.

Its probe, eight certified orbits at 20,000 ranks: the ceiling binds at roughly
half of all ranks, zero violations, **max carry 19-24**, mean slack `~4.5`
divisors -- "the ceiling binds without obstructing" -- and attainment against a
prefix-matched control gives `z = +0.62`.

### The generic verdict is not new information

`GapAvoidanceReductionAndEquidistribution.md` section 3 concludes:

> There is no congruence, height, phase, density, ownership, window, **or carry**
> signal distinguishing safe from fatal orbits, because there is no signal.

`tau_A(n) <= d(n) - 1` against `Q_n = 2 Q_{n-1} + t_n - tau_A(n)` is a **carry
signal** in exactly that sense, and section 3 names the carry explicitly. So M8's
`z = +0.62` and its "binds without obstructing" are what section 3 predicts, not
evidence about M8 specifically. That half of the probe adds nothing, and section 3
lives in the *other* directory, which is why the census did not apply it.

### What genuinely survives in M8, stated fairly

M8 is **not** only a signal claim, and it should not be dismissed as one. Its
substance is an **arithmetic forcing** hope: that `d(n) - 1 < 2 Q_{n-1} + t_n`
holding on a suitable index set forces the carry upward *by an amount the
arithmetic of `n` fixes*, without appeal to any statistical bias. Section 3 kills
signal-based discrimination; it says nothing about a deterministic forcing
identity. That half is untouched.

But the probe bounds what such a forcing could deliver: the carry never exceeds
**24** over 20,000 ranks on any of eight orbits, so whatever the ceiling forces
upward is compensated at the highly-divisible ranks.

### CORRECTION to this section, measured

An earlier revision of this section said the index set the multiplicity screen
demands "is where `d(n)` is largest and the ceiling slack widest". **That is
backwards**, and the correction favours M8. The canonical set meeting every dyadic
block `(n, 2n]` is the **primes** (Bertrand) -- M8 names them itself -- and there
`d(p) = 2`, so the ceiling reads `tau_A(p) <= 1`. Measured on the certified `1/21`
support at depth 4000 (`|A| = 2026`, `1 not in A` confirmed):

| index set | mean slack `d(n) - 1 - tau_A(n)` |
|---|---|
| all `n >= 2` | **4.121** (consistent with the census's `~4.5` at depth 20000) |
| **primes** | **0.525** |

and at primes the slack takes only the values `{0, 1}`, attained (slack `0`) at
**47.5%** of them. The reason is exact: with `1 not in A`, a prime `p` has
`tau_A(p) = 1_A(p)`, so **the ceiling at a prime IS set-ness at that prime** --
there is no slack in the inequality at all, only the binary question of whether
`p in A`.

So the screen-mandated index set is where the ceiling is **tightest**, not widest.
On it the carry recursion reads

    Q_p = 2 Q_{p-1} + t_p - 1_A(p),

i.e. at every prime the carry nearly doubles and can be paid down by **at most 1**.
That is M8's mechanism at its sharpest, sitting exactly on the set its own screen
requires. Whether the compensation at composite ranks can always absorb it is the
open question -- but the tension I previously reported does not exist.


**Nonclaim.** Not a kill. M8 remains the census's best entry and this section does
not close it; it separates the half that is already answered from the half that is
not, and names the tension the forcing half must resolve.

## 19. M8's forcing cannot contradict by aggregation -- it is squeezed between a triviality and section 3

Section 18 left M8's forcing half open: `tau_A(n) <= d(n) - 1` against
`Q_n = 2 Q_{n-1} + t_n - tau_A(n)`, `Q_n >= 0`. This section bounds what that
forcing can deliver.

### The aggregate form is exactly `y <= T_1`

The ceiling gives `Q_n >= 2 Q_{n-1} + t_n - (d(n) - 1)` at every rank. Iterating
from `Q_0 = 0`,

    Q_N  >=  sum_{n=1..N} 2^(N-n) ( t_n + 1 - d(n) ).

Divide by `2^N`. Their own probe caps the carry at 19-24 over 20,000 ranks, so
`Q_N / 2^N -> 0`, giving

    0  >=  sum_{n>=1} ( t_n + 1 - d(n) ) / 2^n  =  y + 1 - sum_n d(n)/2^n.

And `sum_n d(n)/2^n = E` exactly -- the Lambert identity
`sum_n d(n) x^n = sum_k x^k/(1 - x^k)` at `x = 1/2`, verified to 16 digits
(`1.6066951524152917`). So the entire aggregate content of M8's ceiling is

    y  <=  E - 1  =  T_1  =  0.6066951524152918.

**Which is immediate from `1 not in A`:** `y = sum_{a in A, a >= 2} z_a <= sum_{a >= 2} z_a = T_1`.
The ceiling, aggregated, carries no information beyond the hypothesis that put it
there. Their eight probe targets clear it with slack `0.11` to `0.56`:

| target | `y` | slack to `T_1` |
|---|---|---|
| `1/21` | 0.0476 | 0.5591 |
| `1/2` | 0.5000 | **0.1067** |
| `4/9` | 0.4444 | 0.1623 |
| `13/37` | 0.3514 | 0.2553 |

### Why no aggregation can do better

Every way of summing the ceiling -- over all `n`, over the primes only, over any
index set with any weights -- produces an **upper bound on `y`**, because the
recursion is linear in `tau_A` and `y` is its generating value. But `y` is a free
parameter ranging over `(0, T_1)`. An upper bound on a free parameter is never a
contradiction. **So no aggregated form of M8 can close.**

This explains the probe's own headline exactly: *"the ceiling binds without
obstructing"*. Binding constrains the **size** of `y`, and every candidate target
sits comfortably inside the bound.

### The pincer

> M8's forcing half is squeezed. Its **aggregate** form is the trivial bound
> `y <= T_1`. Its **dynamical** form -- which ranks the ceiling binds at, in what
> order -- is exactly what GapAvoidance section 3 says carries no signal.

This does not kill it: a deterministic argument about the *order* of binding is
not a statistical-signal claim, and section 3 does not reach it. But it names what
such an argument must do -- exploit the sequence of binding ranks without relying
on any bias in that sequence -- and it rules out the entire class of
sum-the-inequality arguments, which is where a first attempt would naturally go.

**Nonclaim.** Not a kill, and no new bound on 257. It closes the aggregation route
inside M8 and leaves the dynamical route, now the only thing standing in the
census.

## 20. `hclose` is an Erdos COVERING SYSTEM problem -- and T14a's band is closed by exhibition, not by its stated mechanism

**First, what this section does not claim.** Most of this iteration re-derived T14
from scratch -- the closed form `Phi_A(N) = sum_{d in A} 2^(N mod d)/(2^d - 1)`,
the gap wall `excess >= 2^-(a+(N) - N)`, and the `A = N` witness. All three are
already T14, which I wrote. **That part was a rehash and counts as nothing.**
Their `Psi_n` with `rho_k(n) = (-n) mod k` is the same object as `Phi_A(N)`:
`2^-rho_k(n) c_k = 2^r/(2^k - 1)` for `r = n mod k > 0`, and `1/(2^k - 1)` when
`k | n`. Confirmed term by term.

### The exact two-part form

Since the term for `d` is **exactly zero** when `d | N`, small elements of `A`
cannot obstruct once `N` is chosen to absorb them. Writing
`L_J = lcm(A n [1, J])`:

> **`hclose` holds iff for every `J` there is an `N` with `L_J | N` such that no
> element of `A` exceeding `J` divides any of `N+1, ..., N+J`.**

Equivalently, `hclose` FAILS iff for some `J` the congruences

    N = -j  (mod d),    d in A n (J, inf),   1 <= j <= J

**cover every multiple of `L_J`** -- an Erdos covering system with all moduli
exceeding `J` and each modulus used at most `J` times. A grep for `covering
system`, `minimum modulus`, `Filaseta`, `Balister`, `Sahasrabudhe` across both
programmes and the Lean corpus returns **zero** hits, so this framing is new here.
(`CoveringBoundary.md` is the Kovac-Tao *Kakeya* covering -- a different sense.)

### Why T14a's mechanism does not settle the band

T14a concludes the band "unbounded gaps + divergent reciprocal sum" is "NOT
open -- it was closed by the same mechanism." The mechanism is: some `d in A`
with `d !| N` divides `N+j` for bounded `j`. For `A = P` that is immediate --
`N+1 > 1` has a prime factor, it lies in `A`, and it cannot divide `N`. **For a
general divergent-reciprocal-sum `A` nothing supplies it**: the mechanism is
exactly the assertion that the covering above exists, which is what was to be
shown.

### The witness, and my own instrument error

`A = {p prime : p = 1 mod 4}` has divergent reciprocal sum (Dirichlet) and gaps
tending to infinity, so it **passes** T14's gap wall and sits precisely in the
disputed band. First measurement: longest run of consecutive integers with no
prime factor `= 1 mod 4` is **4**, flat from `10^3` to `10^7`. That number is an
artifact -- `5 = min A`, and every 5 consecutive integers contains a multiple of
5. **Wrong index set**: when `5 | N` the `d = 5` term is exactly zero, so 5
cannot obstruct. The correct search fixes `L_J | N` and excludes only `A n (J, inf)`:

| `J` | `L_J` | first `N = M L_J` with `[N+1, N+J]` free of `A n (J,inf)` |
|---|---|---|
| 5 | 5 | `N = 5` (M=1) |
| 13 | 65 | none, `M <= 400000` (`N <= 2.6 x 10^7`) |
| 17 | 1105 | none, `M <= 400000` |
| 29 | 32045 | none, `M <= 400000` |
| 37 | 1185665 | none, `M <= 400000` |
| 41 | 48612265 | none, `M <= 400000` |

So T14a's **conclusion holds on this witness**, and the reason is quantitative,
not the stated mechanism: integers with no prime factor `= 1 mod 4` have density
`~ c/sqrt(log x) -> 0`, so a whole window of length `J` being free has
probability decaying like `(log N)^(-J/2)`.

**Caveat, the dual of T12.** A finite search can never refute existence. The
candidate density `(log N)^(-J/2)` against `X/L_J` candidates means any witness
would be astronomically large; absence up to `2.6 x 10^7` is not a proof.

### What this changes

The band is not closed by a mechanism; it is closed **one `A` at a time, by
exhibiting the covering**. The general statement needed is: *for every infinite
`A` outside the solved classes, the interval-residue system with moduli
`A n (J, inf)` covers `L_J Z` for some `J`.* Systems with all moduli exceeding a
bound are exactly what Hough's minimum-modulus theorem and the
Balister-Bollobas-Morris-Sahasrabudhe reciprocal-sum bounds constrain -- and
those constrain coverings from **existing**, i.e. they push toward `hclose`
HOLDING, i.e. toward 257 being TRUE on this band. The multiplicity is `J`, so the
distinct-moduli theorems do not transfer unchanged; that gap is the concrete
next question.

**Nonclaim.** No new solved class, and T14a's verdict is not overturned -- only
its justification. The one-way content is the reduction of the disputed band to a
covering-system existence question with all moduli `> J`, plus the correction that
divergent reciprocal sum alone does not supply T14a's mechanism.

## 21. The T14a band is NOT closed: an explicit harmonically divergent `A` where `hclose` HOLDS

Section 9 of DivisorTransformRecovery proves the conditional wall -- *if* for
every large `N` some `d in A` with `d !| N` divides `N + j` for bounded `j`, then
`hclose` fails -- and verifies it for `A = P` and for bounded-gap `A`. Its
closing line then says **"The uncovered band that looked open after section 8 was
not open."** That is an overreach, and this section refutes it constructively.
Divergent reciprocal sum does not imply `A`'s multiples nearly cover.

Section 9's own table already contains the escape: `powers_of_two` reaches excess
**exactly 0** with max run 1, purely by the `d | N` route at `N = lcm`. Powers of
two are reciprocal-summable, so that instance sits inside an already-solved class
and looked like a curiosity. **It is not a curiosity -- the same route runs on a
divergent support**, because of one fact:

> The harmonic mass of a block `[B, B(1 + 1/j)]` is `~ log(1 + 1/j) ~ 1/j`,
> which depends only on the **ratio**, not on the scale `B`.

So block scales may be pushed as fast as we like -- fast enough to outrun the
lcm -- while the reciprocal sum still diverges.

### Theorem (tower-block class). PROVED.

*Set `B_1 = 2`, and recursively*

    C_j  = { a in Z : B_j <= a <= B_j (1 + 1/j) },
    L_j  = lcm( C_1 u ... u C_j ),
    B_{j+1} = L_j + j,            A = union_j C_j .

*Then (a) `sum_{a in A} 1/a = infinity`; (b) `A` has unbounded gaps and natural
density 0; (c) `hclose` holds; hence (d) `sum_{a in A} 1/(2^a - 1)` is irrational,
by the machine-checked reduction `..._of_infinite_of_shiftedAtom_closeReturn`.*

**Proof of (c).** Take `N = L_j`. For `a in C_1 u ... u C_j` we have `a | L_j = N`,
so `N mod a = 0` and that term of `Phi_A(N)` is `1/(2^a - 1)` -- *identical* to its
term in `Phi_A(0) = y`. It contributes nothing to the excess. For `a in C_i` with
`i > j` we have `a >= B_{j+1} = L_j + j > N`, so `N mod a = N` and the excess from
that term is `(2^N - 1)/(2^a - 1) < 2^(N - a + 1)`. Summing over all such `a`,

    excess(L_j)  <  2^(N+1) * sum_{a >= B_{j+1}} 2^-a  =  2^(N + 2 - B_{j+1})
                 =  2^(L_j + 2 - L_j - j)  =  2^(2 - j)  ->  0.   QED

**(a)** `sum_{a in C_j} 1/a >= (B_j/j) / (B_j(1 + 1/j)) >= 1/(2j)` once `B_j >= 2j`,
and `sum_j 1/(2j)` diverges. **(b)** the gap from `max C_j` to `B_{j+1} = L_j + j`
grows without bound since `L_j >= max C_j`; density at `X = max C_j` is `~ 1/j -> 0`.

### Numerical confirmation of the mechanism, exact rationals

With `C_1 = {6,7}` (so `L_1 = 42`) and `C_2 = {60,61,62}` (`min 60 > 42`):

| `N` | `a in A` dividing `N` | excess `Phi(N) - y` | predicted `2^(N - min(a>N))` |
|---|---|---|---|
| `L_1 = 42` | `6, 7` | `6.6757e-06` = `2^-17.2` | `2^(42-60) = 2^-18` |

**The margin is load-bearing.** A first toy put the next block only 1 above
`L_2 = 794220`; the excess was then `0.75 = 2^-0.4`, not small. The recursion must
use `B_{j+1} = L_j + j`, not `B_{j+1} = L_j + O(1)` -- which is exactly why the
construction needs stating rather than gesturing at.

### What this changes

1. **T14a and section 9's Consequence are wrong on the band.** The correct
   statement is: `hclose` fails for bounded-gap `A`, for `A = P`, and generally for
   near-covering `A`. It does **not** fail throughout "unbounded gaps + divergent
   reciprocal sum".
2. **A new class where 257 is PROVED**, disjoint from the three solved classes --
   it is aperiodic, not base-adapted, and harmonically **divergent**.
3. **The counterexample profile in section AO is insufficient.** A counterexample
   must be aperiodic, not base-adapted, harmonically divergent, and not eventually
   periodic -- and now also **not tower-separated**. Harmonic divergence was being
   treated as the property that escapes `hclose`; it is not. What escapes `hclose`
   is near-covering, and divergence is neither necessary nor sufficient for that.

**Nonclaim.** The class is artificial and proves nothing about a general `A`. The
one-way content is the refutation of a recorded closure, plus the consequent
correction to what a counterexample must satisfy.

## 22. `hclose` is exactly the RECURRENCE of the word `tau_A` -- and no measure criterion can decide it

### The characterisation

Since the `d`-term of the excess is **exactly zero** when `d | N`, a small excess
forces, for every `d in A` with `d !| N`, that the next multiple of `d` after `N`
is far. At `N = L_w = lcm(A n [1,w])` every `d <= w` divides `N`, and no larger
`d` may divide `N+1, ..., N+w`. Both conditions together say precisely

    tau_A(N + j) = tau_A(j)    for j = 1, ..., w.

> **`hclose` holds iff the word `tau_A = 1_A * 1` is RECURRENT** -- iff every
> prefix of `tau_A` occurs again later.

Check against the known cases. `1 !in A` gives `tau_A(1) = 0`, so recurrence
demands `N+1` be `A`-free infinitely often. For `A = P` that reads
`omega(N+1) = 0`, i.e. `N + 1 = 1`: **`tau_P` is non-recurrent**, which is exactly
T14a's proposition, now as a one-line consequence rather than a separate argument.
A grep for `recurrent`, `B-free`, `subshift`, `Sarnak`, `Lemanczyk` across both
programmes returns nothing, so this framing is new here; it is the standard object
of the `B`-free subshift literature (Sarnak's programme; Kulaga-Przymus-Lemanczyk-Weiss).

### Why the measure route cannot decide it

Recurrence of a word has a classical sufficient condition: if `x` is generic for a
shift-invariant measure giving every prefix cylinder positive mass, **Poincare
recurrence** returns the prefix. That route decides `hclose` only when the good `N`
have **positive density**. It is tempting because it would import the whole
`B`-free machinery. It cannot work, and section 21's construction proves it:

- For the tower-block `A`, the good `N` at level `j` is essentially the **single
  point** `N = L_j`. The next multiple `2 L_j` already exceeds `B_{j+1} = L_j + j`,
  so it is not good. The good set is one point per level -- **density zero**.
- Yet `hclose` HOLDS there, with `excess(L_j) < 2^(2-j)` (section 21, proved).

> So `hclose` is satisfied on a density-zero set of times. Every criterion phrased
> in terms of density, genericity, Behrend-ness, or the measure of a cylinder is
> **blind to it**: those criteria see a null set and report failure, while the
> criterion holds.

This is a fresh instance of T10 -- the measure/genericity trap recurring in
disguise -- and it is now proved specifically for `hclose` rather than suspected.

### What this eliminates and what it leaves

**Eliminated.** Any attempt to decide `hclose` via the density of `A`-free
integers, via Behrend-ness of `A`, via the Mirsky/Haar measure of the `B`-free
system, or via genericity of `tau_A`. All are positive-density instruments aimed
at a density-zero phenomenon. Section 9's own table is consistent with this and
does not distinguish the routes: `powers_of_two` scores excess `0.000000` with max
run `1`, which is the positional route, not the density route.

**Left standing.** The positional question: *for which `A` does the word `tau_A`
return to its prefix at all, however sparsely?* The two known producers are
summability (long runs) and lcm-divisibility (section 21). The two known
obstructions are bounded gaps (T14) and near-covering (`A = P`, T14a).

**Nonclaim.** No new solved class beyond section 21, and no decision for any `A`
not already decided. The one-way content is the identification of `hclose` with
word recurrence, and the elimination of the entire measure-theoretic family of
criteria by an explicit density-zero witness.

## 23. Two rows of section 9's table displayed the same zero and meant opposite things

Section 9's measured table reports min excess `0.000000` for both
`multiples of 30` and `powers of two`, and its prose reads *"Both routes to a
small excess are visible: `multiples_of_30` wins by long runs, `powers_of_two`
wins by divisibility at `N = lcm`."* Exact rational recomputation:

| family | true min excess | as `N -> infinity` | verdict |
|---|---|---|---|
| multiples of 30 | `9.313226e-10` = **exactly `2^-30`** | stuck at `2^-30` | **`hclose` FAILS** |
| powers of two | `5.42e-20` at `N = 64` | `~ 2^-N -> 0` | **`hclose` HOLDS** |

`2^-30 = 9.313226e-10` to every digit -- the T14 gap bound, hit exactly, because
`A = 30Z` has gaps bounded by 30. At `N = 30m` the index `k = m+1` always yields a
term `(2^(30m) - 1)/(2^(30(m+1)) - 1) ~ 2^-30`, so the infimum is bounded away from
zero for the **infinite** set, no matter how large `N` grows.

So the row that section 9 offered as a *witness for the long-run route* is in fact
a set that section 8 had already **killed** by the bounded-gap wall. The 29-long
run is real and irrelevant: runs cannot help when the next element of `A` after `N`
is always within 30. The only genuine witness in that table is `powers of two`, and
it wins by the `d | N` route -- the same route section 21 generalises to a
harmonically divergent support.

**Why the display hid it.** Six decimal places cannot separate `2^-30` from `0`, and
a finite cap makes it worse: truncating `A` at 2000 turns `A` into a finite set whose
lcm divides some `N`, at which the excess is **exactly** 0. The instrument reported
convergence where the infinite object has a positive floor. Fixed in section 9 by
printing the value and its limit behaviour rather than a rounded scalar.

**Nonclaim.** No verdict changes for any `A` -- `multiples of 30` was already
excluded by section 8, and `powers of two` was already known summable. The one-way
content is that a load-bearing table cited by T14a listed a killed set as a witness,
and that the two routes are distinguished by the limit, never by a value at one `N`.

## 24. The magnitude criterion `a+(w)` vs `L_w` is REFUTED -- `hclose` is a residue condition, not a size condition

Section 22 left the positional question: for which `A` does `tau_A` return to its
prefix at all? The natural first guess compares the least element of `A` past `w`
with the lcm below it. Write `a+(w) = min{a in A : a > w}` and
`L_w = lcm(A n [1,w])`. Section 21's tower has `a+(w) = L_w + w > L_w`, and powers
of two have `a+(w) = 2 L_w`, only a factor 2 clear -- which made
`a+(w) > L_w` infinitely often look close to necessary.

**It is not necessary.** Take

    A = {2, 3} u {2^k : k >= 2}.

For `2^m <= w < 2^(m+1)` we get `L_w = lcm(2,3,4,...,2^m) = 3 * 2^m` while
`a+(w) = 2^(m+1) = 2 * 2^m`, so `a+(w) < L_w` at **every** scale `m >= 2`. Yet with
`delta_a(N)` the distance from `N` up to the next multiple of `a` (the term is
exactly 0 when `a | N`), integer arithmetic gives

| `m` | `L_w` | `a+(w)` | `a+ < L_w` | `delta_min(L_w)` | excess at `N = L_w` |
|---|---|---|---|---|---|
| 4 | 48 | 32 | yes | 16 | `3.05e-05` |
| 6 | 192 | 128 | yes | 64 | `1.08e-19` |
| 8 | 768 | 512 | yes | 256 | `1.73e-77` |
| 9 | 1536 | 1024 | yes | 512 | `1.49e-154` |

`delta_min = 2^m -> infinity`, so the excess `~ 2^(-2^m) -> 0` and **`hclose` HOLDS**
at `M = 1`. No absorbing multiplier is needed.

### Why no magnitude criterion can work

At `N = L_w = 3 * 2^m` we have `N mod 2^(m+1) = 2^m`, so
`delta = 2^(m+1) - 2^m = 2^m` -- `N` sits at the **midpoint** residue of the
dangerous modulus, maximally far from a multiple of it. The size of `a+(w)`
relative to `L_w` carries no information about `N mod a+(w)`, and the criterion
depends on nothing but that residue. A magnitude comparison is simply the wrong
invariant.

What makes this `A` work is alignment: `L_w = 3 * 2^m` shares the factor `2^m` with
**every** element of `A n (w, inf)` at once, so one choice of `N` puts the whole
tail at a controlled residue simultaneously. That is precisely section 20's
covering-system condition, and this section confirms it is the right frame -- the
magnitude shortcut past it is dead.

### Two instrument notes, both fired here

- My first run printed a *control* row at `M = 1` labelled "bounded, `hclose` would
  FAIL on this sequence". Reading the numbers, `delta_min` there was `4, 8, 16, 32,
  64, 128` -- **growing**, not bounded. The label was false and the control was in
  fact a second witness. Never label a row without reading it.
- The excess table underflows to `0.000e+00` in double precision for `m >= 10`
  (`< 1e-308`). That is underflow, not zero -- the same trap as section 23, one
  iteration later, in a table I wrote myself.

**Nonclaim.** `A = {2,3} u {2^k}` is reciprocal-summable, so `hclose` for it was
never in doubt; the refuted object is the proposed *characterisation*, not any
verdict. No new solved class. The one-way content is the elimination of every
magnitude-based criterion for `hclose`, with the reason: the condition lives on
residues, and the free multiplier acts on residues.

## 25. The carry identity is INFORMATION-FREE -- why section 19 and the integrality handle both collapsed

### The handle I proposed, and its collapse

Last iteration I recorded a handle for the near-covering regime: if `y = p/q` has
eventual binary period `l`, then `{2^(N+l) y} = {2^N y}`, so from
`R(N) = Q_N + {2^N y}`,

    R(N + l) - R(N)  =  Q_{N+l} - Q_N  in  Z    for all large N,

i.e. `sum_{d in A, d !| l} (2^((N+l) mod d) - 2^(N mod d))/(2^d - 1)` is an integer,
a sum of terms each lying in `(-1, 1)`. It looks like a strong Diophantine
constraint. **It is empty.**

Evaluate it at `N` a multiple of `L_w = lcm(A n [1,w])`. Every `d <= w` has
`N mod d = 0` and `(N+l) mod d = l mod d`, so those terms are
`(2^(l mod d) - 1)/(2^d - 1)`, **independent of `N`**. Extending over all `d`
(terms with `d | l` vanish identically) the sum is

    sum_{d in A} (2^(l mod d) - 1)/(2^d - 1)  =  Phi_A(l) - y  =  rho(l).

And `rho(l) = Q_l` by the very decomposition `R = Q + frac`, with
`{2^l y} = {y} = y` for purely periodic `y < 1`. So the "constraint" says
`Q_l in Z` -- **true by definition, for every `A`, with or without rationality.**

### The pattern, and the elimination

This is the second time in one session. Section 19 aggregated M8's ceiling and
obtained exactly `y <= T_1`, which is immediate from `1 !in A`. Here differencing
the same identity obtains `Q_l in Z`, immediate from `Q` being the carry. The two
failures share a cause:

> `R(N) = Q_N + {2^N y}` with `Q_N in Z_{>=0}` is a **definition** -- it defines
> `Q_N = floor(R(N))` and `{2^N y} = {R(N)}`. Every consequence obtained by
> manipulating that identity alone -- summing, telescoping, differencing across a
> period, dividing by `2^N` -- is automatically satisfied and carries **no
> information about `A`**.

Information enters only through an **independent arithmetic constraint** on `tau_A`
or on the digits: the ceiling `tau_A(n) <= d(n) - 1` from set-ness, the gap
structure of `A` (T14), near-covering (T14a), primitive prime divisors of `2^d - 1`,
Bang/Zsygmondy. Those are the load-bearing inputs; the recursion is the bookkeeping
that carries them, never a source.

**Fourth elimination.** Alongside aggregation (s19), measure/density (s22), and
magnitude (s24): **carry-identity manipulation** is now closed as a class. A future
iteration proposing a condition derived purely from the carry recursion plus
integrality should evaluate it at `N = M L_w` first; if the `N`-dependence
disappears, the condition is a restatement.

### Status of the capped task

`cap_quick_erdos_257_open_the_erdos_1948_mechanism_4be6eeb4dae6` remains OPEN on its
main question -- what property of `tau_A` the Erdos 1948 argument consumes, given
that `hclose` provably fails for `A = N_{>=2}` where 1948 succeeds. Only its
*concrete handle* is closed, by this section. The corpus's recorded 1948 searches
(`ElementaryCriterionBoundary.md` section 6) were aimed at whether particular
families -- `{2^j + 1}`, Golomb's `G`, Mahler's method, Duverney, Fermat numbers --
are covered by known criteria; none of them opened the mechanism.

**Nonclaim.** No progress on 257 this iteration, and no new class decided. The
one-way content is negative and methodological: a handle I had recorded as live is
dead, and the reason generalises to a whole family of arguments.

## 26. The Erdos 1948 mechanism, OPENED -- it is the three certificate sockets, and it runs on MULTIPLICATIVITY

Closes the handle-free half of
`cap_quick_erdos_257_open_the_erdos_1948_mechanism_4be6eeb4dae6`. Source:
J. Vandehey, *On an incomplete argument of Erdos on the irrationality of Lambert
series*, arXiv:1206.0340, which reconstructs the 1948 argument in order to finish
its `b < -1` case. Erdos' original: J. Indian Math. Soc. (N.S.) **12** (1948) 63-66.

### What Erdos actually proved, and by what criterion

> Erdos proved that for any integer `b > 1` the value `f(1/b)` is irrational **by
> showing that `f(1/b)` written in base `b` contains arbitrarily long strings of
> 0's without terminating on 0's completely.**

For `y in (0,1)` with binary digits `t_n`, a run of `K` zeros starting at position
`N+1` is exactly `frac(2^N y) < 2^-K`. So arbitrarily long zero-runs, with the
expansion not eventually all-zero, is precisely

    liminf_N frac(2^N y) = 0.

**That is the condition sections 1-2 proved the three certificate sockets collapse
to.** The corpus's three machine-checked sockets ARE the Erdos 1948 criterion. All
~14 corpus citations of Erdos 1948 use it as a black-box *result*; none identifies
it with the socket condition the corpus itself carries.

This also settles the warning I flagged and nearly violated: the sockets
(`liminf frac(2^N y) = 0`) and `hclose` (`liminf Phi_A(N) = y`) are different
conditions, and now their standing is asymmetric. **`hclose` provably fails in the
near-covering regime (T14, T14a). The socket condition SUCCEEDS there -- Erdos
proved it for `A = N_{>=2}`.** The sockets, not `hclose`, are the route into the
regime `hclose` cannot reach.

### The engine, and the exact property it consumes

Vandehey p.3, following Erdos: fix `k = floor((log N)^(1/10))`; take primes
`p_i > (log N)^2` and set `A := prod p_i^b`; by CRT choose `r` with

    r + j  ==  prod_{i = j(j-1)/2+1}^{j(j+1)/2} p_i^(b-1)   (mod  prod p_i^b).

Then for every integer of the form `r + mA`,

    d(r + mA + j)  ==  0   (mod b^(j+1)),      0 <= j < k,

*"by the multiplicativity of `d(.)`"*. The kernel of the trick is

> `p^(b-1) || n`  implies  `b | d(n)`,

since that prime contributes the factor `(b-1) + 1 = b` to `d(n) = prod (e_i + 1)`;
stacking `j` such primes by CRT gives `b^j`. Divisor counts divisible by high powers
of `b` at `k` CONSECUTIVE integers make those digit contributions vanish, and a
tail estimate (Vandehey Lemma 2.2, "Erdos also proved this") bounds what follows.
That is where the long zero-run comes from.

### Why this does not transfer, and the exact generalisation target

`tau_A = 1_A * 1` is multiplicative **iff `1_A` is**. For a general infinite `A` it
is not, and step (1) of the argument -- the only step that produces the zero-run --
is exactly the multiplicative step. So:

> **The single method known to reach the near-covering regime is powered by
> multiplicativity of the coefficient sequence, which a general `A` destroys.**

That is a precise account of why 257 is hard, and it converts the vague "different
criterion needed" (T14, DivisorTransformRecovery.md sections 8-9) into one concrete
question:

> **Can one force `2^(j+1) | tau_A(n)` at `k` consecutive `n`, for a general
> infinite `A`?** For `A = N` this is Erdos' CRT-plus-multiplicativity construction.
> For general `A`, `tau_A(n)` is a divisor COUNT restricted to `A` and obeys no
> product formula, so the construction has no direct analogue -- but the target is
> now stated in the corpus's own coordinates.

### Prior art the corpus should carry

Vandehey Theorem 1.1: for `b > 1`, any finite set `Acal` of non-negative integers,
and any sequence `{a_n}` in `Acal` not ending on repeated 0's, `sum d(n) a_n / b^n`
is irrational -- Erdos' method, stronger conclusion, "virtually identical proof".
Theorem 1.2 drops `0` from `Acal` and allows negative entries, finishing the
`b < -1` case. **Note the shape difference: those series are `sum d(n) a_n b^-n`
with `a_n` bounded, whereas ours is `sum tau_A(n) 2^-n`.** They coincide only when
`tau_A(n) in {0, d(n)}`. Vandehey also poses an open question directly adjacent to
ours: replace `a_n in Acal` by `0 <= a_n <= phi(n)` and find the fastest growing
`phi` for which Theorem 1.1 survives -- our `tau_A(n) <= d(n) - 1` (section 19) is a
constraint of exactly that type.

**Nonclaim.** Nothing here proves or disproves 257, and no new class is decided. The
one-way content is the identification of the socket condition with Erdos' 1948
criterion, the isolation of multiplicativity as the property his argument consumes,
and the resulting concrete generalisation target.

## 27. Erdos' mechanism and `hclose` are INCOMPARABLE -- witnesses on both sides

### The transplant, stated exactly

A zero-run of length `K` at position `N` is `frac(R(N)) < 2^-K`. If

    2^k | tau_A(N + k)      for k = 1, ..., K,

then every `tau_A(N+k) 2^-k` with `k <= K` is an **integer**, so
`frac(R(N)) = frac(sum_{k>K} tau_A(N+k) 2^-k) <= 2^-K R(N+K)`, and since
`R = O(log N)` this tends to 0. That is Erdos' `b^(j+1) | d(r + mA + j)` in our
coordinates. It is **sufficient** for the zero-run, and section 26 identified the
zero-run criterion with the three sockets.

### Why it is robust for `A = N` and fragile for a count

**Robustness (exact).** If `b | d(n)` and `q` is prime with `q !| n`, then
`d(n q^e) = (e+1) d(n)`, so `b | d(n q^e)`. **Uncontrolled extra prime factors
cannot destroy the forced congruence** -- multiplicativity absorbs them. Checked:
28525 pairs `(n, q)` with `8 | d(n)`, `q` prime, `q !| n` -- **28525 preserved, 0
destroyed.** This is why Erdos need only control `O(k^2)` primes by CRT and may
ignore the cofactor entirely.

**Fragility.** `tau_A` is a COUNT, not a product: one uncontrolled `A`-divisor
shifts it by exactly `+1` and destroys any congruence. For `A = P`,
`tau_P(nq) = tau_P(n) + 1` for every new prime `q`. Density of `n <= 2 x 10^6` with
`2^k | f(n)`, `f != 0`:

| `k` | `A = N`, `f = d` (multiplicative) | `A = P`, `f = omega` (a count) |
|---|---|---|
| 2 | 0.860861 | 0.218907 |
| 3 | **0.533186** | **0.000000** |
| 4 | 0.219912 | 0.000000 |
| 5 | 0.057980 | 0.000000 |

Empty from `k = 3` because `max omega(n) = 7` in that range and `2^k | omega(n)`
with `omega != 0` forces `omega(n) >= 2^k`, i.e. `n >= primorial(2^k) ~ e^(2^k)`.

### The transplant is NOT a universal route -- a 2-adic obstruction

Take `A = {2^j : j >= 1}`, so `tau_A(n) = v_2(n)`. Counting `N < 2 x 10^6` for which
`2^k | v_2(N+k)` holds for all `k <= K`:

| `K` | 1 | 2 | 3 | **4** | 5 |
|---|---|---|---|---|---|
| count | 1333332 | 399999 | 66666 | **0** | **0** |

and the reason is exact, not a search limit: if `v_2(N+1) >= 2` then `N+1 = 4u`, so
`N+3 = 4u+2` has `v_2` **exactly 1**, while `k = 3` demands `8 | v_2(N+3)`. Two
positions two apart cannot both carry high `v_2`. **The transplant is empty at
`K = 4` for this `A`.**

### Incomparability

Yet `A = {2^j}` **is** decided, and `hclose` decides it: section 9 / section 23 give
excess `5.42e-20` at `N = 64`, decaying like `2^-N`, by the `d | N` route at
`N = lcm`. Meanwhile `A = N_{>=2}` is decided by Erdos 1948 and `hclose` provably
**fails** there (T14: `N+1 in A` forces excess `>= 0.4`). So:

| `A` | Erdos-transplant zero-run | `hclose` |
|---|---|---|
| `N_{>=2}` | **works** (Erdos 1948) | **FAILS** (T14) |
| `{2^j}` | **empty at `K = 4`** (2-adic, above) | **works** (`~2^-N`) |

> **Neither mechanism subsumes the other.** Section 26 said the sockets, not
> `hclose`, reach the near-covering regime; that stands. This section adds the
> converse: `hclose` reaches sets where the term-by-term transplant is provably
> empty. They are incomparable, with explicit witnesses both ways.

A third, disjoint mechanism is already recorded in the corpus:
`ElementaryCriterionBoundary.md` section 6 attributes `sum_j 1/(2^(2^j) - 1)` to the
Mahler/Duverney line, which runs on **multiplicative self-similarity** of the
support -- available for `{2^j}`, absent for a general `A`.

### What I could NOT establish, stated plainly

I wanted to conclude the transplant is *not necessary* for the socket condition,
which needs the socket condition to HOLD for `{2^j}`. **Irrationality does not imply
it** -- the sockets are sufficient, not necessary -- so that inference is invalid.
Direct measurement of `y = sum_j 1/(2^(2^j) - 1) = 0.403936827882...`: the record
run of zero binary digits is `4` through the first 4000 places and `5` by 5800.
Consistent with the transplant failing there, but by T12's dual a finite depth
neither confirms nor refutes unbounded runs. **No claim either way.**

**Nonclaim.** No new class decided and no verdict changed. The one-way content is
the incomparability with witnesses on both sides, the exact robustness/fragility
dichotomy explaining why the transplant is confined to multiplicative coefficients,
and the 2-adic proof that it is empty at `K = 4` for `{2^j}`.

## 28. ERDOS HIMSELF STATES THE PRIMES CASE OPEN -- `sum_p 1/(2^p - 1)` is `sum nu(n)/2^n`

Answers `cap_quick_erdos_257_is_there_a_third_mechanism_sta_61510002e66f`. Source:
P. Erdos, *On the irrationality of certain series: problems and results*, 1988
survey, p.102 (`renyi.hu/~p_erdos/1988-22.pdf`) -- a scanned PDF, unreadable to text
extraction but legible page-by-page.

### The quote

> "It is very annoying that I cannot prove that `sum_{n=1}^inf nu(n)/2^n` is
> irrational; **perhaps here I am overlooking a simple argument**."

`nu(n)` is the number of distinct prime factors. And `nu = tau_P`, so

    sum_{n>=1} nu(n) 2^-n  =  sum_{p prime} 1/(2^p - 1).

Verified: both equal `0.5169428198056404`, agreeing to `5e-121` at truncation depth
400 (the residual is the truncation tail, nothing else).

**So `A = P` -- the single most natural infinite support -- is OPEN, stated open by
Erdos himself, in the very survey `ElementaryCriterionBoundary.md` section 6 already
lists among its searched sources.**
**CORRECTED, same session.** I first wrote that the corpus had no note of this. That was
WRONG. The corpus owns it under the modern notation: `S(P) = sum_m omega(m) 2^-m` is
**Erdos problem #69**, recorded in `ElementaryCriterionBoundary.md` section 2 and in
`erdos257_hole_geometry/notes/DiophantineReduction.md`, together with Pratt's conditional
result -- and it is USED THERE AS A FALSIFIER. `ElementaryCriterionBoundary.md` line 416
kills its own lcm-criterion argument precisely because that argument "would give
`Sum_p 1/(2^p - 1) = Sum_m omega(m) 2^-m` irrational unconditionally -- i.e. Erdos problem
**#69**, which Pratt proved only under a uniform prime `k`-tuples conjecture. Something is
wrong", and then diagnoses the real flaw: an `l`-adic valuation cannot be read off a series
that converges in `R` and not in `Q_l`. **My novelty sweep searched Erdos' `nu` notation and
not the corpus's `omega`** -- a notation mismatch, not an absence.

What genuinely IS absent from the corpus, and is what this section contributes: the Erdos-1988
wording itself (including "perhaps here I am overlooking a simple argument"), the adjacent
Chowla / Borwein / `2^n - 3` / `n! - 1` statements below, the explicit `nu = omega = tau_P`
bridge, and the `excess(1) = y` identity.

### Why this is the sharpest frontier statement available

All three known mechanisms fail at `A = P`, and now we know the case is open:

| mechanism | status at `A = P` |
|---|---|
| `hclose` / prefix recurrence | **fails** -- T14a, any prime dividing `N+1` forces excess `>= 1/3` |
| Erdos-1948 transplant (`2^k | tau_A(N+k)`) | **empty** -- needs `omega(n) >= 2^k`, i.e. `n >= primorial(2^k) ~ e^(2^k)` |
| Mahler / Duverney self-similarity | **inapplicable** -- `P` is not multiplicatively self-similar |

That is a complete account: the primes sit outside every route the programme knows,
and Erdos could not reach them either. **Any claim that 257 is "one mechanism away"
must first explain the primes.** Conversely Erdos' own "perhaps I am overlooking a
simple argument" is a standing invitation on a sub-case far more tractable than the
full problem -- and one where a positive answer would be a named Erdos problem
settled, not a generalisation of 257.

### Adjacent statements from the same page, worth carrying

- **Chowla's conjecture**: `sum d(n)/t^n = sum 1/(t^n - 1)` irrational for every
  *rational* `t > 1`. Erdos: "almost certainly true but is unattackable by my
  methods." (He proved it for integer `t > 1`.)
- **Borwein, June 1987**: `sum 1/(2^n + r)` is irrational for every rational `r`.
- Erdos cannot prove `sum 1/(2^n - 3)` or `sum_{n>=2} 1/(n! - 1)` irrational.
- `sum phi(n)/2^n` and `sum sigma(n)/2^n` -- "no doubt also irrational but this is
  probably unattackable by my methods." Note these are NOT of our form: `phi` and
  `sigma` are not `1_A * 1` for any set `A`.

### Instrument note -- section 9's `0.516943` is a universal constant, not a fact about `P`

The primes row of section 9's table reports min excess `0.516943`, which is *equal to
`y` itself*. That is not a coincidence and not an error: for any `A` with `1 !in A`,
every `a >= 2` has `1 mod a = 1`, so

    Phi_A(1) = sum_a 2/(2^a - 1) = 2y,   hence   excess(1) = y,   for EVERY such A.

The minimum over `1 <= N <= 150` is attained at `N = 1`, so the reported figure is
the universal `N = 1` value and carries **no information about the primes
specifically**. T14a's proof is unaffected -- it rests on `p | N+1` forcing
excess `>= 1/3` at every `N`, not on the measured minimum. Do not read `0.516943` as
evidence about `P`; and do not confuse it with the sum of reciprocals of Mersenne
*primes* (`0.5164...`), a third and unrelated quantity.

**Nonclaim.** Nothing here proves or disproves anything. The one-way content is that
the primes case is Erdos-open, that all three known mechanisms provably miss it, and
that a load-bearing measured constant in section 9 is universal rather than
diagnostic.

## 29. Pratt's mechanism, OPENED -- it is a SHIFTED close-return, and the corpus's socket has no shifted form

The corpus cites Pratt (arXiv:2409.15185) for its *result* -- Erdos #69 conditional on
prime `k`-tuples -- in at least three places, and uses it as a falsifier. It nowhere
carries the *mechanism*. Read directly (pp. 1-4; the sieve estimate proving Lemma 2.2
is beyond what I read).

### The construction

**Theorem 1.3** (Pratt). Assume Conjecture 1.2 (quantitative prime `K`-tuples with
uniformity: coefficients `a_k, b_k <= (log x)^100` and `K <= 100 log log x`). Then
`sum_n omega(n)/t^n` is irrational for every integer `t >= 2`.

Set `K = floor(5 log log x)` and `Q = prod_{p <= K} p^ceil(log K / log p)`, chosen so
that **`k^2 | Q` for every `k <= K`**. Proposition 2.1 supplies `n_0 <= x` with

1. `n_0 Q/k + 1` is **prime** for every `1 <= k <= K`;
2. `omega(n_0 Q + k) <= (log log x)^2` for `K < k <= L`;
3. `omega(n_0 Q + K + 1) > (1/10) log log x`.

The pivot is a factorisation:

    n_0 Q + k  =  k ( n_0 Q/k + 1 ),

and the two factors are **coprime** -- because `k^2 | Q` gives `k | Q/k`, so
`n_0 Q/k + 1 = 1 (mod k)`. With (1) the second factor is prime, so by additivity of
`omega`,

> **`omega(n_0 Q + k) = omega(k) + 1`, EXACTLY, for every `k <= K`.**

### Why that closes

With `N = n_0 Q` and `T(N) = b sum_k omega(N+k)/t^k in Z` (this is `b R(N)`; `T(N)` is
an integer precisely because `alpha = a/b`), split `T = S_1 + S_2 + S_3`. The head
block becomes

    S_1 = b sum_{k<=K} omega(k)/t^k + b sum_{k<=K} 1/t^k
        = a - b sum_{k>K} omega(k)/t^k + b sum_{k<=K} t^-k
        = a + b/(t-1) + O(log K / t^K),

i.e. **the tail reproduces the head**, plus the geometric constant `1/(t-1)`. Then
`T(N) = a + b/(t-1) + S_2 + E` with `|E| << log K / t^K`. Two branches:

- `(t-1) !| b`: then `b/(t-1)` is not an integer while `S_2, E = o(1)`. Contradiction.
- `(t-1) | b`: then `a + b/(t-1) in Z`, so `S_2 + E` must be an integer -- but it is
  `o(1)` and **strictly positive**, the lower bound `S_2 >= b log log x / (10 t^{K+1})`
  coming from condition (3). Contradiction.

**At our base `t = 2` the first branch is vacuous** -- `t - 1 = 1` divides every `b` --
so the entire weight sits on the second, i.e. on condition (3): a single index in the
middle range carrying an anomalously large `omega`. That is the load-bearing hypothesis
at base 2, and it is exactly where the prime-tuples uniformity is spent.

### The transplantable core

> `hclose` demands `tau_A(N+k) = tau_A(k)` for `k <= K`, i.e. `R(N) -> y`.
> Pratt achieves `tau_A(N+k) = tau_A(k) + 1`, i.e. **`R(N) -> y + 1/(t-1)`**, and
> closes with a *certified-nonzero* `o(1)` remainder rather than a vanishing one.

So the criterion is a **shifted close-return**, and the shift is what a sum-of-two-parts
factorisation buys. The corpus has no shifted form: `ReciprocalSupportIrrationality.lean`
requires closeness to `Phi_A(0)` itself, and its `shiftedSupportAtom` "shift" is the
`N mod d` inside the atom, an entirely different sense of the word. A grep for an
additive-shift return finds nothing.

**Actionable consequence.** The machine-checked socket could be widened from
`inf_N Phi_A(N) = Phi_A(0)` to `inf_N Phi_A(N) = Phi_A(0) + c` for an explicit constant
`c` that is not an integer, or -- the branch that matters at `t = 2` -- to a return with
a remainder proved nonzero and `o(1)`. Whether the Lean proof survives that weakening is
a concrete, bounded question, and it is the first widening of the socket suggested by
anything outside the programme.

**Nonclaim.** Pratt's theorem is his and is conditional on prime `k`-tuples; nothing
here is unconditional and nothing decides 257. The one-way content is the extraction of
the mechanism, the identification of it as a shifted close-return, and the observation
that the corpus's socket admits no shift -- with the widening stated as a specific
target rather than a claim.

## 30. The socket DOES widen -- the integer-gap endgame survives any INTEGER shift, which is exactly Pratt's case at base 2

Answers `cap_quick_widen_the_lean_close_return_socket_to_a_46fb76273fe5`. Read the
proof body, `ReciprocalSupportIrrationality.lean:901-951`.

### What the machine-checked engine actually is

The socket at line 938 is a **thin wrapper**. The content is

    theorem irrational_binaryCoeffSeries_of_strictInitialMin_of_closeReturn
      (c : N -> N) (hgrowth : forall n, c n <= n)
      (hstrict : forall N, 0 < N -> binaryCoeffTail c 0 < binaryCoeffTail c N)
      (hclose  : forall eps > 0, exists N > 0,
                   binaryCoeffTail c N < binaryCoeffTail c 0 + eps) :
      Irrational (binaryCoeffSeries c)

and its proof is an **integer-gap endgame**, five steps:

1. assume rational; obtain `v > 0` and an integer orbit `u` with `u N = v * tail(N)`
   (`temperedBinaryOrbit_eq_scaledTail`);
2. instantiate `hclose` at `eps = 1/v`;
3. `hgap_pos`: `u N - u 0 > 0`, from **`hstrict`**;
4. `hgap_lt`: `u N - u 0 < 1`, from the close return at `1/v`;
5. `omega`: no integer lies in `(0, 1)`.

The wrapper supplies `hstrict` from infinitude of `A`
(`binaryCoeffTail_supportCoeff_zero_strictMinimum`, witness any `d in A` with `d > N`)
and passes `hclose` through unchanged.

### The widening, and its exact condition

Replace the two hypotheses by their shifted forms, for a constant `c0 >= 0`:

    hstrict' : forall N > 0,  tail(0) + c0 < tail(N)
    hclose'  : forall eps > 0, exists N > 0, tail(N) < tail(0) + c0 + eps

Steps 3 and 4 then give `v*c0 < u N - u 0 < v*c0 + 1`, and step 5 closes **iff the
open interval `(v*c0, v*c0 + 1)` contains no integer** -- i.e. iff `v*c0 in Z`. Since
`v` is produced existentially inside the proof and cannot appear in a hypothesis, the
usable condition is hypothesis-side:

> **`c0` an integer.** Then `v*c0 in Z` for every integer `v`, and steps 1-5 go through
> **verbatim**. `c0 = 0` recovers the present theorem.

Note the direction, which is the opposite of the naive guess: an **irrational** shift
would leave exactly one integer inside `(v*c0, v*c0+1)` and **kill** the argument. It is
integrality of the shift that saves it.

### Why this is exactly Pratt's case

Section 29: Pratt's return is to `y + 1/(t-1)`, and at `t = 2` the shift is
`1/(t-1) = 1` -- **an integer**. His own first branch (`(t-1) !| b`) is vacuous at base 2
for the same reason, and he closes instead on a remainder proved nonzero and `o(1)`.
That is step 3 and step 4 of the endgame above, with the positivity supplied by his
Proposition 2.1(3) rather than by infinitude of `A`. **The two arguments are the same
endgame**; the corpus's engine already has the right shape and merely states its
hypotheses at shift zero.

### What this does and does not buy

**Does.** The machine-checked engine is strictly more general than its statement: it
proves irrationality from a shifted strict minimum plus a shifted close return, for any
integer shift. Nothing in steps 1-5 touches the value of the shift beyond the
integrality of `v*c0`.

**Does not.** It supplies no new `hstrict'`. At shift `c0 = 1` the strict half now reads
`tail(0) + 1 < tail(N)` for every `N > 0`, which is far stronger than the shift-zero
version and is **false** for supports whose tail returns near `tail(0)` -- e.g. any `A`
satisfying `hclose` itself. So the widened socket is not a superset of the present one:
the two are for different supports, and a support must be shown to sit under one or the
other. Pratt gets his positivity from prime `k`-tuples, which is exactly the cost.

**Nonclaim.** I did not edit the Lean file and ran no build; this is an analysis of the
existing proof body, checkable by reading `:901-932`. No new class is decided, and the
widened socket is useless without a source of `hstrict'`.

## 31. The flagship theorem is weaker than its own proof: `hstrict` is used at ONE `N`, not globally

Continuing the read of `ReciprocalSupportIrrationality.lean:901-932`. The hypothesis

    hstrict : forall N : N, 0 < N -> binaryCoeffTail c 0 < binaryCoeffTail c N

is a **global strict minimum** -- it quantifies over every positive shift. But trace
where it is consumed. Line 915 obtains a single witness,

    obtain <N, hN, hnear> := hclose (1 / (v : R))

and the only occurrence of `hstrict` in the entire proof is line 919, inside `hgap_pos`,
applied as **`hstrict N hN`** -- at that one `N`. Steps 4 and 5 never mention it again.

> **So the proof establishes a strictly stronger theorem than the one stated.** The two
> hypotheses can be merged into a single two-sided condition at a common witness:
>
>     hreturn : forall eps > 0, exists N > 0,
>                 binaryCoeffTail c 0 < binaryCoeffTail c N
>                                     < binaryCoeffTail c 0 + eps
>
> and `irrational_binaryCoeffSeries_of_strictInitialMin_of_closeReturn` follows from it
> unchanged, since the merged form supplies exactly `hstrict N hN` and `hnear` for the
> same `N`.

### Why the weakening matters

The global form demands strictness at **every** positive shift; the merged form demands
it only along the returning subsequence. For the support wrapper this costs nothing --
infinitude of `A` gives the global statement anyway
(`binaryCoeffTail_supportCoeff_zero_strictMinimum`, witness any `d in A` with `d > N`) --
so the flagship corollary is unaffected. It matters for **other coefficient sequences
`c`**, where a global strict minimum may fail while a two-sided return still holds: the
engine is a general statement about `binaryCoeffSeries c` for any `c` with `c n <= n`,
and that generality is currently gated behind a hypothesis the proof does not use.

Combined with section 30, the honest description of the machine-checked engine is:

> irrationality follows from **a single sequence of witnesses `N` at which the tail
> exceeds `tail(0) + c0` and approaches it arbitrarily closely**, for any integer shift
> `c0 >= 0`.

That is a two-parameter weakening of the stated theorem, both parameters free, and both
verified by reading the proof rather than by re-proving it.

**Nonclaim.** I have not edited the Lean or run a build; this is a claim about which
hypotheses the existing proof term consumes, checkable at `:901-932`. It changes no
verdict for any `A`, because the support wrapper supplies the global form regardless.
The value is that the engine is reusable at strictly lower cost than its signature
advertises -- relevant precisely when a future route supplies returns without a global
minimum, which is the shape section 29 found in Pratt.

## 32. LANDED: the generalised endgame is machine-checked

Sections 30 and 31 were analyses of a proof term. They are now theorems.
`ReciprocalSupportIrrationality.lean`, commit `8bf6751f`, **+70 lines, 0 deletions**:

    theorem irrational_binaryCoeffSeries_of_shiftedTwoSidedReturn
        (c : N -> N) (hgrowth : forall n, c n <= n) (c0 : N)
        (hreturn : forall eps > 0, exists N > 0,
           binaryCoeffTail c 0 + c0 < binaryCoeffTail c N
                                    < binaryCoeffTail c 0 + c0 + eps) :
        Irrational (binaryCoeffSeries c)

    theorem irrational_binaryCoeffSeries_of_strictInitialMin_of_closeReturn_of_shifted
        ... := by
      refine irrational_binaryCoeffSeries_of_shiftedTwoSidedReturn c hgrowth 0 ?_
      ...

Both weakenings in one statement: **any natural shift `c0`**, and a **two-sided return
at a single witness** in place of the global strict minimum. The second theorem
re-derives the previously stated form as the `c0 = 0` case, so the weakening is
verified rather than asserted, and nothing downstream is disturbed.

**Receipts.** `lake build Erdos257PeriodNoncollapse.ReciprocalSupportIrrationality`
returned **captured `rc = 0`**, 3023 jobs, both before and after the edit;
`#print axioms` on both new theorems reports
`[propext, Classical.choice, Quot.sound]` -- **no `sorryAx`**. A baseline build was run
first, so the green is a delta and not an inherited state. Per the standing rule, only
the captured `rc` is treated as proof; the `error` matches in the log are the identifier
`sternBrocotDepthMass_error`.

**Two process notes.**

1. The build environment is live and warm -- toolchain `v4.29.1`, 8410 oleans cached,
   56 GiB free. **An earlier note of mine claiming the Mathlib cache had expired
   (`643M, 1 olean`) is stale**; `lake build` runs directly, no `cache get` needed.
2. `scoped_commit` refused with `rc = 2` and
   `status=missing_required_receipt`: **active Lean claims require a navigation
   adoption receipt before commit**. The refusal names its own remediation, and running
   `mathematical_working_memory --claim-first --claim-session-id <id> --mode auto` issued
   receipt `wln_5dbc08710f2d4935` (`recorded_exact_active_claim_match`,
   `valid_for_active_claims: true`), after which the commit went through. This gate is
   specific to Lean paths and does not fire on prose commits -- worth knowing before the
   next Lean edit.

**Nonclaim.** This decides nothing about 257 and adds no solved class. The engine is now
*stated* at the generality its proof always had. It remains useless without a source of
shifted positivity -- section 30's warning stands: at `c0 = 1` the lower bound
`tail(0) + 1 < tail(N)` is far stronger than the shift-zero version and fails for
exactly the supports that satisfy the unshifted return. Pratt buys his from prime
`k`-tuples; nothing unconditional is known to supply it.

## 33. The widened socket at `c0 = 1` IS Pratt's hypothesis -- and the primes approach that level

### A collapse I nearly claimed, and why it is wrong

First attempt: since `Phi_A(1) = 2y` universally (section 28), the quantity
`iota(A) := inf_{N>0} Phi_A(N) - Phi_A(0)` obeys `iota <= y < 1`, so
`iota in Z_{>=0}` forces `iota = 0` -- the widening would collapse to `hclose` and
section 32's Lean work would be vacuous for support series.

**That argument is wrong.** It conflates the infimum offset with the hypothesis.
Section 31 established that strictness is consumed only **at the returning witness**,
so `hreturn` at shift `c0` does not say the infimum sits at `y + c0`; it says the
**level** `y + c0` is a limit point of `{R(N)}` **from above**. A bound on the
infimum constrains nothing about accumulation at a higher level. Recorded because it
fired: the two readings differ exactly when the return is non-minimal, which is
Pratt's case.

### The right measurement

For each family, `inf { R(N) - (y + c0) : N > 0, R(N) > y + c0 }` over `N < 1.2e6`,
`K = 60` (dropped tail `< 1e-16`, below float noise):

| `A` | `c0 = 0` | `c0 = 1` | `c0 = 2` |
|---|---|---|---|
| `P` (primes) | `0.51694` (`N=1`) | **`1.096e-3`** (`N=420`) | **`1.63e-6`** (`N=452286`) |
| `N_{>=2}` | `0.60670` (`N=1`) | `0.10043` (`N=4`) | `0.01153` (`N=24`) |
| `{2^j}` | **`0.00000`** (`N=32`) | `0.01494` | `0.02156` |

Three readings, and they agree with everything already established:

1. **`{2^j}` attains gap `0` at `c0 = 0`** -- `hclose` holds there, as section 9/23 record
   (`~2^-N` at `N = 64`). The instrument reproduces a known verdict.
2. **`N_{>=2}` has no small gap at any `c0`.** Consistent: `hclose` fails (T14) and Erdos
   reaches that case by his own 1948 route, not by a return.
3. **`P` fails `c0 = 0` -- its `c0 = 0` entry is the universal `N = 1` value `y` again,
   not data -- but approaches `y + 1` to `1e-3` and `y + 2` to `1.6e-6`, the latter at
   `N = 452286`, i.e. the approach sharpens as the window grows.**

### Why row 3 matters

Section 29: Pratt's construction returns to `y + 1/(t-1)`, which at `t = 2` is exactly
`y + 1`. Row 3 is that return, visible numerically. So:

> **The widened socket `irrational_binaryCoeffSeries_of_shiftedTwoSidedReturn` at
> `c0 = 1`, instantiated at `c = omega`, is precisely the hypothesis Pratt establishes
> under the uniform prime `k`-tuples conjecture.**

That is what section 32's Lean generalisation is *for*. `8bf6751f` is the right shape to
host a formalisation of Pratt's theorem: the endgame is done and machine-checked, and
what remains is Proposition 2.1 -- the CRT construction plus the tuples hypothesis --
which enters as an assumption, not as a proof.

### The falsifier, respected

**No claim is made that `hreturn` holds for `A = P`.** Proving it unconditionally *is*
Erdos #69, which is open (T20/T20a), and the corpus's own falsifier
(`ElementaryCriterionBoundary.md` line 416) kills any argument that would deliver it
for free. The numbers above are consistent with the hypothesis and say nothing about
provability; by T12's dual a finite window bounds the gap from above only, so a small
gap is evidence FOR accumulation and a large one is evidence AGAINST, and neither is
proof.

**Nonclaim.** No new class decided, nothing unconditional, and the `c0 = 0` column is
partly the universal `Phi_A(1) = 2y` identity rather than measurement. The one-way
content is the corrected reading of `hreturn` as an accumulation-from-above condition,
the identification of the `c0 = 1` instance with Pratt's hypothesis, and the resulting
statement of what a Lean formalisation of #69 would now require.

## 34. `lake build` here is a GUARDED shim, and `rc = 75` is a lease deferral, not a compile failure

### The finding

I drafted the arithmetic core of Pratt's construction and built it. The build returned
**`rc = 75` with zero `error:` lines**. That is not a compile failure. In this project
`lake` is a wrapper around `scripts/lean_fast_build.py`, and the payload was:

    schema: command_run_capacity_deferred_v0
    status: validation_capacity_deferred
    conflict_keys: ["lean-project-build:formal_math/erdos257_period_noncollapse"]
    ticket_id: rct_550ecaa24213c553cf5b
    proof_scope: not_proof_evidence
    forbidden_actions: ["attached_capacity_wait", "retry_loop", "ticket_polling", "raw_lake_bypass"]
    next_action: record_validation_pending_and_continue_disjoint_work
    reentry_condition: "no active owner holds lean-project-build:formal_math/..."

A **sibling agent held the project build lease**. The guard forbids waiting, retrying,
polling the ticket, and bypassing to raw `lake`; it instructs recording the pending
validation and continuing with disjoint work.

**Correction to my own note from earlier today.** Section 32 recorded "`lake build`
runs directly, no `cache get` needed." True but incomplete, and the incompleteness is
the dangerous part: `lake` is **guarded**, and a green build means you *held the lease*,
not that the command is unconditional. Both earlier builds (baseline and post-edit)
happened to acquire it.

**Unification with a known code.** `rc = 75` is already the repo's admission-refusal
code for `repo-pytest` -- "refused to launch, not a test failure." The same code carries
the same meaning here for Lean builds. The general rule: **`rc = 75` in this repo means
REFUSED TO RUN, never RAN AND FAILED.** A future agent reading it as a compile error
would start "fixing" Lean that was never compiled -- the log's own
`proof_scope: not_proof_evidence` is the tell.

### What was drafted, and its status

**UNVERIFIED.** The patch is held at
`scratchpad/pratt_core_draft.patch` (75 lines) and the Lean file was **reverted to
`HEAD`**, deliberately: a dirty Lean file in a project whose build lease another agent
holds can break that agent's build. The three lemmas drafted:

- `coprime_succ_of_dvd : k ∣ m → Nat.Coprime k (m + 1)`;
- `coprime_cofactor_of_sq_dvd : 0 < k → k*k ∣ Q → Nat.Coprime k (n * (Q / k) + 1)`,
  the step that makes the block factorisation work, since `k*k ∣ Q` gives `k ∣ Q/k`;
- `card_primeFactors_block_of_sq_dvd : 0 < k → k*k ∣ Q → (n*(Q/k)+1).Prime →
  (n*Q + k).primeFactors.card = k.primeFactors.card + 1`,

the last being **Pratt's shift identity** -- `omega(n*Q + k) = omega(k) + 1` exactly --
via `n*Q + k = k * (n*(Q/k) + 1)` with coprime factors. The prime `k`-tuples input
enters only as the primality hypothesis, exactly as intended: the arithmetic core is
unconditional, the tuples conjecture supplies `hp`.

Known defect in the draft, to fix on re-entry: the `a ≠ 0` argument in the
`card_primeFactors_mul_of_coprime` application was written as a malformed pipeline
expression and needs `hk.ne'` instead.

**Nonclaim.** No Lean landed this iteration and none of the three lemmas is verified.
The one-way content is environmental: `rc = 75` is a lease deferral with a forbidden
retry, the `lake` entry point is guarded rather than raw, and section 32's
characterisation of it was incomplete.

## 35. A sibling audited the same claim and we disagree on one row -- the derivation settles it

`ConsolidatedAccount.md` (commit `eacb4810`) section 6.1 item 3 audits the same upstream
claim my section 12 audits -- `ProgrammeSpine` CORRECTION 2's "the same constant 1
appears **three independent times**". Two independent verdicts, reached without contact:

| | verdict |
|---|---|
| their 6.1 item 3 | "**numerology.** The covering constant and the measure constant are the *same* limit; the third item, `1/E = 0.6224`, is **not `1` at all**. Two-thirds double-counting, one-third wrong" |
| my section 12 | all appearances are one geometric identity `sum_{j>=1} t^-j = 1/(t-1)`, which at `t = 2` reads `2 - 1 = 1` |

**We agree on the main point** -- the appearances are not independent -- and we agree
that the covering constant and the measure constant are the same limit. We disagree on
`1/E`, which they call "not `1` at all" and my row 3 records as inheriting the constant
through its numerator.

### The derivation decides it, in their own lane's favour of my row

`HoleGenericity.md` line 78:

    prod_{n=1..N} (1 - h_n)  =  T_N / T_0  =  T_N / E  ->  1/E = 0.6223956041...

with `T_0 = E`. For that limit to be `1/E`, the numerator must tend to **1** -- and it
does, as `lim 2^N T_N = measure(Acal) = 1`, which is exactly row 2 of my table. So the
`1` in `1/E` is **not a bare numeral**: it is the measure constant, arriving through the
telescoping product. Row 3 stands, and their "one-third wrong" is the imprecise half of an
otherwise correct audit.

**Caveat, stated because the source is loose.** The quoted line writes `T_N / T_0` without
the `2^N` rescaling, and unrescaled `T_N -> 0`, so `T_N/E -> 0` rather than `1/E`. The
line is therefore either using a rescaled `T_N` or eliding the factor; the limit it asserts
is only correct with the rescaling, under which the numerator is `lim 2^N T_N = 1`. **I am
reading it with the rescaling**, which is the only reading that makes the stated limit true
and is consistent with `measure(Acal) = lim 2^N T_N = 1` elsewhere in the same programme.

### What this is worth

Not much mathematically -- neither verdict changes any route. It is worth recording for
two reasons. First, **two agents audited the same claim independently and converged on the
substance**, which is weak but real evidence that the "one identity in four dresses"
reading is right rather than my own numerology. Second, the residual disagreement was
resolvable **by reading the derivation rather than by arguing from the value**: `0.6224`
is indeed not `1`, and that observation is true and irrelevant, because the question was
never whether `1/E` equals `1` but whether the constant `1` occurs inside it for a reason.

**Nonclaim.** No route changes, no class decided. The one-way content is a resolved
cross-document disagreement and the confirmation of section 12's row 3 against an
independent audit that called it wrong.

## 36. LANDED: Pratt's shift identity is machine-checked

Commit `69628273`, `ReciprocalSupportIrrationality.lean`, **+69 lines, 0 deletions**,
`lake build` captured **`rc = 0`**, 3023 jobs, **0 `sorryAx`**. Five lemmas, with axioms:

| lemma | axioms |
|---|---|
| `coprime_succ_of_dvd : k ∣ m → Nat.Coprime k (m+1)` | `[propext, Quot.sound]` |
| `coprime_cofactor_of_sq_dvd : 0<k → k*k ∣ Q → Nat.Coprime k (n*(Q/k)+1)` | `[propext, Quot.sound]` |
| `block_factorisation : 0<k → k ∣ Q → n*Q + k = k*(n*(Q/k)+1)` | **`[propext]`** |
| `card_primeFactors_mul_of_coprime` | `[propext, Classical.choice, Quot.sound]` |
| **`card_primeFactors_block_of_sq_dvd`** | `[propext, Classical.choice, Quot.sound]` |

The last is **Pratt's shift identity**: `0 < k`, `k*k ∣ Q`, and `(n*(Q/k)+1).Prime`
give

    (n*Q + k).primeFactors.card = k.primeFactors.card + 1,

i.e. `omega(n*Q + k) = omega(k) + 1` exactly. The prime `k`-tuples input enters **only**
as the primality hypothesis, so this half is **unconditional**; the conjecture's job is
solely to supply that hypothesis for `k = 1..K` simultaneously.

Combined with the endgame at `8bf6751f` (section 32) and the `c0 = 1` identification of
section 33, what now remains for a machine-checked conditional Erdos #69 is the
**analytic wrapper**: Pratt's Proposition 2.1 as an existence statement (with Conjecture
1.2 as an explicit Lean hypothesis) plus the Lemma 2.2 tail estimate. Both are sieve
analysis; neither is arithmetic.

### Two process notes

**`Nat.dvd_sub'` does not exist at this Mathlib pin.** The draft used it to get
`g ∣ (m+1) - m = 1`. Natural subtraction is the wrong instrument anyway; the fix avoids
it entirely -- `Nat.dvd_add_right h1 : g ∣ m + n ↔ g ∣ n`, so `(Nat.dvd_add_right h1).mp h2`
yields `g ∣ 1` with no truncation semantics in play. **On ℕ, reach for an additive
cancellation lemma before a subtraction one.**

**I applied the patch before reading the preflight verdict, which was `COLLISION`.** That
was an ordering error on my part -- the edit should gate on the verdict. It was harmless
here only because the colliding owner was
`claude-erdos257-pratt-lean-2026-08-22`, **my own session id from the previous
iteration**, left open because that turn's build deferred (`rc = 75`) so its
`scoped_commit` never ran and never closed the claim. Committing under that same session
id was therefore the correct resolution and closed it. **A stale self-claim is the
expected residue of a deferred build** -- read the `owner_sessions` field before treating
a `COLLISION` as foreign, and note that the verdict alone does not distinguish the two.

**Nonclaim.** Nothing unconditional about #69 and nothing about 257. The arithmetic core
of one conditional argument is now machine-checked; the analytic half is not started.

## 37. The `S_1` computation is ONE exact identity, and Lemma 2.2 is not needed for it

Working out what the analytic wrapper actually requires, before formalising it. Pratt
splits `T(N) = S_1 + S_2 + S_3` and estimates each. In our coordinates the first block
collapses to a single **exact** identity with no asymptotics in it at all.

### The identity

Suppose the shift hypothesis holds on an initial block -- `c(N+k) = c(k) + 1` for
`1 <= k <= K`, which for `c = omega` is exactly what the landed
`card_primeFactors_block_of_sq_dvd` (section 36) delivers. Since
`sum_{k>K} c(N+k) 2^-k = 2^-K * tail(N+K)`,

    tail(N)  =  tail(0) + 1 + 2^-K * ( tail(N+K) - tail(K) - 1 ).

**Proof.** Split at `K`; replace `c(N+k)` by `c(k)+1` on the head; the head is
`(tail(0) - sum_{k>K} c(k)2^-k) + (1 - 2^-K)`; both leftover tails are `2^-K` times a
shifted `tail`. Rearranged, that is the display. No limits, no `o(1)`, no estimates --
a finite rearrangement of an absolutely convergent series.

**Calibrated.** On synthetic `c` with the shift imposed only on `1..K` (`K = 12`,
`N = 50`, depth 400, exact rationals): the two sides differ by
`75 / 1.32e123 ~ 5.7e-122`, which is precisely the depth-400 truncation tail. Control
with the hypothesis broken at `k = 3` by `+5`: difference exactly `0.625 = 5 * 2^-3`, the
predicted magnitude -- **so the check has power and is not vacuously passing.**

### What this says about the remaining formalisation

`hreturn` at `c0 = 1` needs `tail(0) + 1 < tail(N) < tail(0) + 1 + eps`, which by the
identity is exactly

    0  <  tail(N+K) - tail(K) - 1  <  eps * 2^K.

Both sides follow from Proposition 2.1 with only **elementary** input:

- **Lower.** 2.1(3) gives `omega(N+K+1) > (1/10) log log x`, so
  `tail(N+K) >= omega(N+K+1)/2 > (1/20) log log x`, while `tail(K) <= log_2 K + O(1)`
  from `omega(n) << log n`. With `K = floor(5 log log x)`, `log_2 K` is
  `log_2(5 log log x)` -- negligible against `(1/20) log log x`. Positive for large `x`.
- **Upper.** 2.1(2) bounds `omega(N+k) <= (log log x)^2` on `K < k <= L`, and
  `omega << log` beyond `L`, so the bracket is `<= (log log x)^2 + O(log x * 2^-(L-K))`,
  against `eps * 2^K` with `2^K ~ (log x)^(5 log 2)`, which grows faster.

> **Lemma 2.2 is therefore NOT needed to derive `hreturn` from Proposition 2.1.** It is
> the sieve estimate Pratt uses to *prove* 2.1 -- i.e. to show the required `n_0` exists.
> The formalisation splits cleanly: **2.1 is the only genuinely analytic obligation**, and
> everything downstream of it is a rearrangement plus `omega(n) << log n`.

That is a sharper statement of the remaining gap than section 36 left, and it means a Lean
development can take 2.1 as a single hypothesis and reach `Irrational` with no further
sieve theory.

### Formalisation note

The identity is the right Lean target: it is finite rearrangement plus the tail-shift
`sum_{k>K} c(N+k) 2^-k = 2^-K tail(N+K)`, and `binaryCoeffTail_succ` already provides the
one-step case in `GenericTailOrbitRigidity.lean`. I have **not** written it; this section
records the target and its calibration only.

**Nonclaim.** Nothing unconditional, nothing about 257, and no Lean landed here. The
one-way content is the collapse of the `S_1` estimate to an exact identity and the
consequent isolation of Proposition 2.1 as the sole analytic obligation.

## 38. LANDED: the shifted-block identity is machine-checked

Commit `1bd41362`, **+66 lines, 0 deletions**, `lake build` captured **`rc = 0`**, 3023
jobs, **0 `sorryAx`**. Three lemmas, all `[propext, Classical.choice, Quot.sound]`:

- `geom_sum_half : ∑ j ∈ Icc 1 K, (1:ℝ)/2^j = 1 - 1/2^K`;
- **`binaryCoeffTail_split`** -- `tail c N = (∑ j ∈ Icc 1 K, c(N+j)/2^j) + tail c (N+K)/2^K`;
- **`binaryCoeffTail_shifted_block`** -- under `∀ j, 1 ≤ j → j ≤ K → c (N+j) = c j + 1`,

      tail c N = tail c 0 + 1 + (tail c (N+K) - tail c K - 1) / 2^K.

That is section 37's identity, and with section 36's `card_primeFactors_block_of_sq_dvd`
supplying the shift hypothesis for `c = omega`, the whole `S_1` half of Pratt's argument
is now machine-checked.

### The route was better than section 37 described

Section 37 called the identity "a finite rearrangement of an absolutely convergent
series". The Lean proof never touches the series. `binaryCoeffTail_succ` gives the
one-step recurrence `tail (N+1) = 2 * tail N - c (N+1)`, so the split is **induction on
`K`** and the infinite sum is never unfolded. Worth stating as a general move: **when a
tail satisfies a one-step recurrence, finite splitting is induction, not summation** --
the analytic content is already spent in whoever proved the recurrence.

### Two Lean lessons, both cost a build

**`field_simp` can defeat `ring` by reordering inside a binder.** The final step failed
with a goal whose two sides differed only by `↑(c x) * 2⁻¹^x` versus `2⁻¹^x * ↑(c x)`
**inside a `Finset.sum`**. To `ring` those are two distinct atoms -- it normalises the
term tree, not sum bodies -- so no amount of `ring` closes it. The identity was a pure
division-ring identity all along (`a/c + b/c` style), so **deleting `field_simp` and
calling plain `ring` closed it immediately**. Reach for `field_simp` only when you
actually need to clear denominators, and never when sums are in play.

**Read the signature of the lemma you are inducting from.** `binaryCoeffTail_succ` takes
`(c) (hgrowth) (N)`; I omitted `hgrowth` from `binaryCoeffTail_split`'s own statement, and
the error surfaced as a type mismatch putting `N + K` in the `hgrowth` slot. A second
error was downstream of the same omission, and a third came from nesting an induction
inside a context whose `ih` then carried `hshift` -- fixed by pulling `geom_sum_half` out
as a standalone lemma. **Inductions want a clean context; hoist them.**

### Where the conditional #69 now stands

Machine-checked: the endgame (`8bf6751f`), the arithmetic core (`69628273`), and now the
`S_1` identity (`1bd41362`). Remaining: Proposition 2.1 as an explicit hypothesis, and the
two elementary bounds of section 37 that turn it into `hreturn` at `c0 = 1`. **No sieve
theory is required downstream of 2.1.**

**Nonclaim.** Nothing unconditional, nothing about 257. Three of the four pieces of one
conditional argument are checked; 2.1 itself is not stated in Lean yet.

## 39. LANDED: the lower half of the shifted return -- and a correction to section 37

Commit `a6e21770`, **+35 lines, 0 deletions**, `rc = 0`, **0 `sorryAx`**, both lemmas on
`[propext, Classical.choice, Quot.sound]`:

- `binaryCoeffTail_ge_head : (c (M+1) : ℝ)/2 ≤ binaryCoeffTail c M` -- immediate from the
  landed split at `K = 1` plus `binaryCoeffTail_nonneg`;
- **`binaryCoeffTail_shifted_block_lower`** -- under the `+1` shift on `1 ≤ j ≤ K`, given
  `binaryCoeffTail c K ≤ B` and `2*(B+1) < c (N+K+1)`, one concludes
  `binaryCoeffTail c 0 + 1 < binaryCoeffTail c N`.

That is the strict lower half of `hreturn` at `c0 = 1`: a single large coefficient just
past the block forces the tail above `tail 0 + 1`.

### The correction

Section 37 said both sides of `0 < tail(N+K) - tail(K) - 1 < eps * 2^K` follow from
Proposition 2.1 "with only **elementary** input". **That is true but incomplete, and the
missing part is not cosmetic.**

The obvious elementary route uses `binaryCoeffTail_le : tail c N ≤ N + 2`, which is
proved from `c n ≤ n` alone. Chasing it: `tail(N+K) ≥ c(N+K+1)/2` and `tail K ≤ K + 2`
give positivity only if

    c (N+K+1)  >  2K + 6.

But `K = floor(5 log log x)` and Pratt's 2.1(3) supplies only
`omega(n_0 Q + K + 1) > (1/10) log log x`, i.e. roughly `K/50`. **The naive route misses by
a factor of about 100 -- it fails, and not narrowly.**

What rescues it is that `tail K` for `c = omega` is not near `K`; it is about
`log_2 K + O(1)`, since `omega(K+j) ≤ log_2(K+j)`. Then `2*(tail K + 1)` is
`O(log K)`, comfortably below `K/50`. **But `omega(n) ≤ log_2 n` is an arithmetic fact
about `omega`, not a consequence of `c n ≤ n`**, and `binaryCoeffTail_le` cannot see it.

So the honest statement of the remaining gap is:

> `hreturn` needs Proposition 2.1 **and** a bound on `binaryCoeffTail c K` that
> `c n ≤ n` does not supply. For `c = omega` that bound is `omega(n) << log n`.

The landed lemma therefore takes `binaryCoeffTail c K ≤ B` as an explicit hypothesis
rather than pretending `binaryCoeffTail_le` covers it. Section 37's "elementary" was
right about the *shape* of the argument and wrong about its *inputs*.

### Where the conditional #69 stands

Machine-checked: endgame (`8bf6751f`), arithmetic core (`69628273`), `S_1` identity
(`1bd41362`), lower half (`a6e21770`). Remaining: the upper half (from 2.1(2)), the
`omega(n) << log n` tail bound, and Proposition 2.1 itself as a hypothesis.

**Nonclaim.** Nothing unconditional and nothing about 257. The lower-half lemma is
conditional on a hypothesis nobody has discharged here.

## 40. LANDED: the upper half, and the per-witness two-sided return

Commit `dbc0a689`, **+38 lines, 0 deletions**, `rc = 0`, **0 `sorryAx`**:

- `binaryCoeffTail_shifted_block_upper` -- under the `+1` shift on `1 ≤ j ≤ K`, from
  `tail c (N+K) ≤ U` and `U - 1 < eps * 2^K`, conclude `tail c N < tail c 0 + 1 + eps`.
  Mirror of the lower half: `tail c K ≥ 0` is all that is needed on the other side.
- **`binaryCoeffTail_shifted_block_two_sided`** -- both halves at a single `N`:

      tail c 0 + 1 < tail c N  ∧  tail c N < tail c 0 + 1 + eps.

That conjunction is **exactly the body of the `hreturn` hypothesis** consumed by
`irrational_binaryCoeffSeries_of_shiftedTwoSidedReturn` at `c0 = 1` (section 32). What
separates the current state from a conditional Erdos #69 is now only the supply of
witnesses, not the shape of the argument.

### The two remaining bounds are the SAME lemma

Worth stating because it halves the remaining work. The two hypotheses still unsupplied
are `tail c K ≤ B` (section 39's missing input) and `tail c (N+K) ≤ U` (Pratt's 2.1(2)).
Both are *"bound a tail from per-coefficient bounds on its own coefficients"* --
`tail c M ≤ (something)` given control of `c (M + j)` for `j ≥ 1`. **One general
tail-bound lemma discharges both.** Its natural forms:

    (∀ j, 1 ≤ j → c (M+j) ≤ B)      →  tail c M ≤ B
    (∀ j, 1 ≤ j → c (M+j) ≤ B + j)  →  tail c M ≤ B + 2

the second being the shape that fits `omega(M+j) ≤ log_2 M + j`.

**Route warning.** `binaryCoeffTail_split` does not suffice: it leaves a
`tail c (M+K)/2^K` remainder, so a bound obtained from it is only as good as the bound on
that remainder -- which is the thing being proved. This one genuinely needs the infinite
sum, via `summable_coeff_shift_tail` (used inside `binaryCoeffTail_succ`,
`GenericTailOrbitRigidity.lean`), bounding the summand pointwise. It is the first piece of
this development that cannot be done by the recurrence alone.

### Where the conditional #69 stands

Machine-checked: endgame (`8bf6751f`), arithmetic core (`69628273`), `S_1` identity
(`1bd41362`), lower half (`a6e21770`), upper half and two-sided packaging (`dbc0a689`).
Remaining: the general tail-bound lemma above, `omega(n) ≤ log_2 n` to instantiate it,
Proposition 2.1 as a hypothesis, and the `∀ eps ∃ N` wrapper.

**Mathlib pin note.** `div_lt_iff₀` is the working name here (not `div_lt_iff`).

**Nonclaim.** Nothing unconditional, nothing about 257. Every landed lemma is conditional
on hypotheses this development does not discharge.

## 41. LANDED: the tail bound -- the one piece that needed the infinite sum

Commit `d7f2c999`, **+31 lines, 0 deletions**, `rc = 0`, **0 `sorryAx`**, axioms
`[propext, Classical.choice, Quot.sound]`:

    binaryCoeffTail_le_of_bound (c) (hgrowth) (M) (B)
      (hb : ∀ j, (c (M + j + 1) : ℝ) ≤ B) : binaryCoeffTail c M ≤ B

Section 40 predicted this would be the first piece unreachable by the recurrence, and
that held: the proof goes through `summable_coeff_shift_tail 2 M c` (CertificateKernel.lean:8573)
for summability of the summand, `Summable.tsum_le_tsum` for the comparison, and
`tsum_geometric_two'` for the majorant. It discharges **both** outstanding hypotheses --
`tail c K ≤ B` of section 39 and `tail c (N+K) ≤ U` of section 40 -- at different
instantiations.

### Three builds, two transferable lessons

**Grep the CORPUS for a lemma name before guessing the Mathlib one.** `tsum_le_tsum`
does not exist at this pin; `Summable.tsum_le_tsum` does, and
`Erdos257PeriodNoncollapse/CurvatureCarry.lean:89` was already calling it exactly that
way. A corpus of 190-odd modules built against the same pin is a better name oracle than
recollection, and it is one grep away. Same family as the earlier
notation-mismatch lesson, pointed at the library instead of the prose.

**Search for the exact statement before proving it by tactic.** I burned two builds
fighting `ring` over `B * 2⁻¹^j` versus `B * (1/2)^j` -- distinct atoms it will not
reconcile, and `simp only [one_div]` did not bridge them either. Mathlib states the fact
outright: `summable_geometric_two'` and `tsum_geometric_two'`. **Expect a normal-form
mismatch when you find it** -- those are phrased `B / 2 / 2^n` against my `B / 2^(n+1)` --
and bridge with a one-line `funext` + `ring` equality of the two functions rather than
reshaping the goal. Fighting a normalisation is always more expensive than proving the
functions equal once.

### Where the conditional #69 stands

Machine-checked: endgame (`8bf6751f`), arithmetic core (`69628273`), `S_1` identity
(`1bd41362`), lower half (`a6e21770`), upper half and two-sided packaging (`dbc0a689`),
tail bound (`d7f2c999`). **Every elementary piece is now done.** Remaining: instantiate
at `c = omega` using `omega(n) ≤ log_2 n`, state Proposition 2.1 as a hypothesis, and
supply the `∀ eps ∃ N` wrapper. Prop 2.1 stays the sole analytic obligation.

**Nonclaim.** Nothing unconditional, nothing about 257. Every landed lemma is conditional
on hypotheses this development does not discharge.

## 42. ASSEMBLED: a machine-checked REDUCTION of Erdos #69 to Proposition 2.1

Commit `19fbd37d`, **+49 lines, 0 deletions**, `rc = 0`, **0 `sorryAx`**. Two lemmas,
the second closing the chain:

    binaryCoeffTail_shifted_block_two_sided_of_coeff_bounds
      -- the two tail hypotheses discharged by binaryCoeffTail_le_of_bound,
      -- leaving only conditions on individual coefficients

    irrational_binaryCoeffSeries_of_shiftedBlockWitnesses
      (c) (hgrowth)
      (hwit : ∀ eps > 0, ∃ N K : ℕ, ∃ B U : ℝ, 0 < N ∧
        (∀ j, 1 ≤ j → j ≤ K → c (N+j) = c j + 1) ∧
        (∀ j, (c (K+j+1) : ℝ) ≤ B) ∧
        2*(B+1) < (c (N+K+1) : ℝ) ∧
        (∀ j, (c (N+K+j+1) : ℝ) ≤ U) ∧
        U - 1 < eps * 2^K) :
      Irrational (binaryCoeffSeries c)

Every hypothesis is now a statement about **individual coefficients** of `c`. No tail,
no series, no analysis appears in the interface.

### What this is, stated exactly

For `c = omega` the shift clause `c (N+j) = c j + 1` is supplied by the landed
`card_primeFactors_block_of_sq_dvd` (section 36), and the remaining four clauses are
exactly what Pratt's Proposition 2.1 delivers. So the development is now a
**machine-checked reduction**:

> Proposition 2.1 (for `c = omega`)  ⟹  `Irrational (sum_n omega(n) 2^-n)` = Erdos #69.

**This is not a proof of #69.** Proposition 2.1 is assumed and never proved; it is where
the uniform prime `k`-tuples conjecture lives, and it remains the sole analytic
obligation. The value of the reduction is that everything *else* is now verified:
the endgame, the shift identity, both bounds, the tail bound, and the assembly --
seven commits, `8bf6751f` through `19fbd37d`, all `rc = 0` and `sorryAx`-free.

### The falsifier, still live

An unconditional derivation of `hwit` for `c = omega` would settle Erdos #69, which is
OPEN (T20/T20a). If a future attempt produces one without a tuples-type hypothesis, it
is wrong, and `ElementaryCriterionBoundary.md:416` is the corpus's own instance of that
error class.

### What a completion would now require

Only two things, in order of difficulty: **(i)** instantiate at `c = omega`, which needs
`omega(n) ≤ log_2 n` to feed `hBK`/`hUK` and `omega(n) ≤ n` for `hgrowth`; **(ii)** state
Conjecture 1.2 and derive Proposition 2.1's four clauses from it -- the CRT construction
of section 29 plus Lemma 2.2's sieve estimate. Step (ii) is a research-scale
formalisation; step (i) is a morning.

**Nonclaim.** Nothing unconditional. Nothing about Erdos 257 itself -- #69 is the primes
sub-case, and section 27 established that the mechanism deciding it does not decide 257.

## 43. LANDED: Erdos #69 stated verbatim, at the witness boundary

Commit `e583cc0c`, **+41 lines, 0 deletions**, `rc = 0`, **0 `sorryAx`**:

    irrational_erdosSupportSeries_two_primes_of_shiftedBlockWitnesses (hwit) :
      Irrational (erdosSupportSeries 2 {p : ℕ | p.Prime})

    irrational_erdosSupportSeries_two_primes_of_omega_witnesses (hwit) :
      Irrational (erdosSupportSeries 2 {p : ℕ | p.Prime})

the second with every hypothesis phrased in `omega` -- `(N+j).primeFactors.card =
j.primeFactors.card + 1`, and so on. That is **Erdos problem 69 verbatim**: irrationality
of `∑_p 1/(2^p - 1)`, conditional on the block witnesses.

### The corpus had already placed this boundary

Searching before deriving paid immediately. `CertificateKernel.lean:9844` already proves
`supportCoeff_primes_eq_card_primeFactors : supportCoeff {p | p.Prime} n =
n.primeFactors.card`, and `:9912` proves
`erdosSupportSeries_primes_eq_tsum_omega : ∑_p 1/(b^p - 1) = ∑_m omega(m)/b^m`, whose
docstring reads: *"The analytic irrationality input is NOT claimed -- this identity places
it at the exact theorem boundary where it belongs."*

**My witness lemma is what consumes that boundary.** Instantiating at
`c = supportCoeff {p | p.Prime}` rather than at a freshly defined `omega` also gives
`hgrowth` for free from the existing `supportCoeff_le_self`, and the `omega` phrasing
follows by `simpa only [supportCoeff_primes_eq_card_primeFactors]`. Had I defined `omega`
myself I would have re-proved two lemmas the corpus already had and landed in a
vocabulary the rest of the programme does not speak.

### `scoped_commit` rc = 3: a THIRD exit-code meaning

The commit returned **`rc = 3`** while printing a hash. It had landed --
`e583cc0c` is in HEAD and its commit object contains both theorems -- but the file showed
`MM`. A probe returned the diagnosis: `transient_git_lock_or_process_contention`, i.e. a
sibling held the git lock and the private-index cleanup could not complete. The index
carried the 41 lines as a **deletion** and the worktree carried them back as an
**addition**; the two cancel, so `git diff HEAD` was empty and `git reset -- <path>`
cleared the artifact with no content at risk.

> **Rule.** When a commit reports non-zero **but prints a hash**, verify against the
> **commit object** (`git show <hash>:<path>`), not the worktree -- the worktree may carry
> unrelated index residue. Then run `git diff HEAD -- <path>`: empty means index artifact
> (safe to `git reset`), non-empty means real uncommitted content.

Three distinct meanings now recorded for `scoped_commit`/build exit codes: **75** =
refused to run (lease deferral, never a failure); **2** = claim collision **or** a
`head_cas` race (retry once -- a race succeeds, a collision repeats); **3** = committed,
but post-commit metadata cleanup blocked by git contention.

### Where the conditional #69 stands

Eight commits, `8bf6751f` through `e583cc0c`, all `rc = 0` and `sorryAx`-free. Remaining:
Proposition 2.1 -- Conjecture 1.2 plus the Lemma 2.2 sieve estimate -- which is
research-scale and is the sole analytic obligation.

**Nonclaim.** Nothing unconditional. The witness hypothesis is assumed; deriving it would
settle an open problem (T20/T20a). And per section 27 this decides #69, **not** Erdos 257.

## 44. RETRACTION: the witness hypothesis was unsatisfiable, and every check passed

**Sections 42 and 43 claimed Erdos #69 was machine-checked-reduced to Pratt's
Proposition 2.1. That claim was false.** From `19fbd37d` onward the reduction rested on a
hypothesis no `c` can satisfy, so the theorems were vacuously true.

The wrapper `binaryCoeffTail_shifted_block_two_sided_of_coeff_bounds` fed the tail-bound
lemma from *pointwise* coefficient bounds. Its hypotheses included both

    hBK  : forall j, (c (K + j + 1) : R) <= B
    hbig : 2 * (B + 1) < (c (N + K + 1) : R)

Instantiate `hBK` at `j = N`. Since `K + N + 1 = N + K + 1`, that gives
`c (N + K + 1) <= B`, and with `hbig`, `2B + 2 < B`, i.e. `B < -2` -- while
`B >= c (K + 1) >= 0`. One instantiation, four lines of Lean. It is now in the file as
`shiftedBlockWitnesses_coeffBounds_unsatisfiable`, which proves `False` from those two
hypotheses alone.

### Nothing in the toolchain could have caught this

Every gate this programme uses passed on the vacuous theorem, and each passed *correctly*:

| Check | Result on the vacuous theorem |
|---|---|
| `lake build` | `rc = 0` |
| `sorryAx` count | `0` |
| `#print axioms` | `[propext, Classical.choice, Quot.sound]` |
| corollary elaborates | yes -- both #69 statements type-checked |

Lean certifies that a proof of `H -> C` is valid. It never asks whether `H` is
satisfiable, and a proof from contradictory hypotheses is perfectly valid. **A conditional
theorem is worth exactly what its hypothesis is worth**, and that worth is not measured by
anything above.

### How it surfaced: applying the theorem somewhere else

Not by re-reading it. By asking whether the same engine reaches Erdos 257 at
`c = tau_A`. It does not, and the reason is structural:

> **For every infinite `A`, `tau_A` is unbounded.** Given `m`, pick `a_1, ..., a_m` in `A`
> and set `n = lcm(a_1, ..., a_m)`; then `tau_A(n) >= m`.

So a hypothesis demanding `tau_A <= B` past some point is unsatisfiable for every infinite
`A` -- the exact class Erdos 257 quantifies over. Turning that same question back on
`c = omega`, which is also unbounded, exposed the contradiction in the #69 wrapper. **Trying
to apply a conditional theorem to a second instance is a satisfiability probe**; it is the
cheapest one available, and it is the one I had not run.

### Scope of the damage, and the repair

Confined to one wrapper. Sound and untouched: `binaryCoeffTail_split`,
`binaryCoeffTail_shifted_block`, `_lower`, `_upper`,
`binaryCoeffTail_shifted_block_two_sided` (which always took **tail** bounds),
`binaryCoeffTail_le_of_bound`, `card_primeFactors_block_of_sq_dvd`, and the endgame
`irrational_binaryCoeffSeries_of_shiftedTwoSidedReturn`. The tail-bound lemma at line 1273
was correct the whole time; only the bridge into it was wrong.

`9825141691` restates the assembly and both #69 corollaries over tail bounds, `rc = 0`,
`sorryAx` 0, all five theorems on `[propext, Classical.choice, Quot.sound]`.

**Why the tail form is not vacuous.** `binaryCoeffTail c K <= B` bounds a weighted sum, so
it forces only `c (N + K + 1) <= B * 2 ^ (N + 1)` -- exponentially weaker than `<= B`, and
leaving `2 * (B + 1) < c (N + K + 1)` satisfiable for `N >= 2`. Likewise `hU` and `hsmall`
demand `B < eps * 2 ^ K`, satisfiable because `2 ^ K` outruns any tail. The tail form is
therefore consistent with unbounded `c`, which is the only form of any use here.

### Standing method rule

For every conditional theorem: **instantiate each universally quantified hypothesis at the
indices that appear in the other hypotheses, and check the conjunction is consistent** --
before claiming the theorem reduces anything. Where a witness is cheap, exhibit one.

**Status after this retraction.** #69 is reduced to Pratt's Proposition 2.1 conditional on
a hypothesis that is now known to be satisfiable in shape, but still assumed and never
proved. The falsifier is unchanged. And per section 27 this decides #69, **not** Erdos 257.

## 45. The shifted-block mechanism is ELIMINATED for Erdos 257

Section 44 left the repaired engine consistent. Consistency is not satisfiability. This
section asks whether the witness hypothesis can actually be met at `c = tau_A`, and the
answer is no -- decisively, at the one support set where the answer is already known.

### The shift clause is a covering condition

**Block reduction.** Let `A` be any support set, `K >= 1`, and `N` divisible by every
`a in A` with `a <= K`. Then for `1 <= j <= K`,

    tau_A(N + j) - tau_A(j) = #{a in A : a > K and a | N + j}.

*Proof.* `tau_A(m) = sum_{a in A} [a | m]`. For `a <= K` we have `a | N`, so
`a | N+j` iff `a | j`, and the terms cancel. For `a > K` we have `a` not dividing `j`,
since `1 <= j <= K < a`, so only `[a | N+j]` survives. QED

So the shift clause `tau_A(N+j) = tau_A(j) + 1` says exactly: **each of
`N+1, ..., N+K` has exactly one divisor in `A` above `K`.** A covering-type condition,
which is the same shape as section 20's characterisation of `hclose`, and not a
coincidence.

**Calibration.** At `A` = primes this reads: each `N+j` has exactly one prime factor
above `K`. Pratt's construction takes `N + j = j * p_j` with `p_j` prime -- the factors of
`j` are all `<= j <= K`, so `p_j` is the unique large one. The reduction reproduces
Pratt exactly, which is the check that it is right.

### The block length must diverge -- machine-checked

`0c2f30e08b` proves `shiftedBlockWitness_forces_small_tail`: chaining the engine's own
four numeric clauses through `binaryCoeffTail_ge_head` gives

    binaryCoeffTail c K < eps * 2 ^ K.

The route is `c(N+K+1)/2 <= tail(N+K) <= U`, `hbig` puts that lower bound above `B + 1`,
and `U - 1 < eps * 2^K` pins `B`, hence `tail_K`, below `eps * 2^K`. No new analysis --
the hypotheses talking to each other. `linarith` closes it.

**A uniform positive lower bound on the tail exists for every support set.** Fix any
`a in A`. Every window `(K, K+a]` contains a multiple of `a`, so some `n` in that window
has `tau_A(n) >= 1`, giving

    tail_K  >=  2^-(n-K)  >=  2^-a      for every K.

`shiftedBlockWitness_forces_large_block` then yields `2^-a < eps * 2^K`, so
**`K > log2(1/eps) - a`**: the block length is forced past every bound as `eps -> 0`. A
support set whose shift blocks are capped at some `K_max` supplies no witness once `eps`
is small, however true the conditional remains.

### At `A = N` the cap is 2, and the classical answer is known

Take `A = N`, so `tau_A = d` and the series is the Erdos-Borwein constant `E`, **proved
irrational by Erdos in 1948**. The shift clause, with no divisibility assumption on `N`:

| `j` | clause | forces |
|---|---|---|
| 1 | `d(N+1) = d(1) + 1 = 2` | `N+1` prime |
| 2 | `d(N+2) = d(2) + 1 = 3` | `N+2 = p^2` |
| 3 | `d(N+3) = d(3) + 1 = 3` | `N+3 = q^2` |

`q^2 - p^2 = 1` forces `(q-p)(q+p) = 1`, impossible for `p >= 2`. **`K >= 3` has no
solutions at any `N` whatsoever.** And `K = 2` forces `N+1 = p^2 - 1 = (p-1)(p+1)` prime,
so `p = 2` and `N = 2`. Max `K = 2`, at one point.

Now make it quantitative. `d >= 1` everywhere gives `tail_K >= sum_j 2^-(j+1) = 1`, so
`delta = 1`, and a witness needs `1 < eps * 2^K <= 4 * eps`. **For every `eps <= 1/4`,
`A = N` admits no shifted-block witness.** The hypothesis quantifies over all `eps > 0`,
so it fails outright.

> **The engine cannot reproduce Erdos 1948.** It fails on the one instance of Erdos 257
> that classical theory settles. A mechanism that cannot recover the known case is not a
> route to the general one.

### Census: the algebra checked against 500,000 starting points

`scripts/shifted_block_census.py`, `n <= 10^6`, `N <= 5 * 10^5`, exact integer arithmetic.
Predictions were written into the script's docstring **before** the run. The control
reshuffles each `tau_A` to preserve its marginal distribution and destroy its arithmetic.

| `A` | predicted | max `K` | at `N` | control |
|---|---|---|---|---|
| `N` (`tau_A = d`) | **2, at `N = 2` only** | **2** | **2** | 1 |
| powers of 2 | **1** | **1** | 1 | 3 |
| primes (`tau_A = omega`) | 3-8, blocks exist | 12 | 840 | 8 |
| `3N` | -- | 1 | 2 | 1 |
| squares | -- | 5 | 39443 | 5 |
| `{3^i}` | -- | 1 | 2 | 10 |

Every prediction held. Three readings the table earns:

1. **`N` and powers of 2 hit their predicted caps exactly**, and the `naturals` argmax did
   not move between a 60,000-point pilot and the 500,000-point run.
2. **For `{3^i}` the control reaches 10 and the real sequence 1**; for powers of 2 it is
   3 against 1. The arithmetic is not merely unhelpful, it is *worse than chance* -- these
   supports actively forbid the coincidences a random sequence stumbles into.
   **[CORRECTED, section 61: VACUOUS, not false. On all four of these cohorts the real
   `K` is a two-line theorem, so this control had POWER EXACTLY ZERO -- no draw could
   have come out otherwise. And the control is a lottery: over 8 seeds powers2 spans
   5..8 and `{3^i}` spans 2..10, so the recorded 3 sits BELOW its own range.]**
3. **Squares score 5 and their control also scores 5.**
   **[RETRACTED, section 61: the squares control spans 4..10 over 8 seeds. This reading
   rests entirely on having drawn a 5. It is an artefact of one draw, not a null.]**
   No structure at all; that row is a
   coincidence count, and reporting it as a block would have been the error the control
   exists to catch.

The one live row is **primes at `K = 12`, argmax `N = 840 = lcm(1,...,8)`** -- a
highly-composite `N`, precisely what the block reduction predicts, and unmoved by an
8.3-fold widening of the search. That is Pratt's mechanism, alive, and it is #69.

### Verdict

**One-way elimination.** The shifted-block engine is not a route to Erdos 257. It demands
blocks of unbounded length; `A = N` caps them at 2 and admits no witness for any
`eps <= 1/4`; and that is the support set whose irrationality Erdos proved in 1948.

**What this does NOT show.** It does not refute 257, and it does not kill the mechanism
for particular `A` -- at the primes it is exactly Pratt's route to #69, still live and
still conditional on Proposition 2.1. It says the mechanism is *instance-specific*, which
is consistent with section 27: transplant and `hclose` are incomparable, and the engine
sits on the transplant side. Erdos's own 1948 criterion -- the three sockets of section 26
-- handles `A = N` and the engine does not, so the two are genuinely different mechanisms
rather than repackagings.

**Nonclaim.** Nothing here is unconditional progress on Erdos 257. Eliminating a mechanism
narrows the search; it does not advance the proof.

## 46. The PARITY OBSTRUCTION -- a complete kill class for the Erdos 1948 mechanism

Section 45 eliminated the shifted-block lane, leaving the socket lane. Section 26 stated
the socket lane's open question in this corpus's own coordinates:

> "Can one force `2^(j+1) | tau_A(n)` at `k` consecutive `n`, for a general infinite `A`?"

This section answers the negative half completely, and the answer is one line of parity.

### The obstruction

A socket run of length `K` at `N` demands `2^k | tau_A(N+k)` for `k = 1, ..., K`. Since
`1 <= k` gives `2 | 2^k`, **every coefficient inside the run is even**. So define

    Odd_A  :=  {m >= 1 : tau_A(m) is odd}.

A run must fit strictly between two consecutive elements of `Odd_A`:

    maxrun  <=  maxgap(Odd_A) - 1.

**Arbitrarily long socket runs require `Odd_A` to have unbounded gaps. If `Odd_A` is
syndetic, the Erdos 1948 mechanism is unavailable for that support set** -- not open,
not unproven: unavailable.

Machine-checked in `54e7fc682b` as `socketRun_excludes_odd_coeff` and
`no_socketRun_of_odd_in_window`. `rc = 0`, `sorryAx` 0, axioms **`[propext, Quot.sound]`
-- no `Classical.choice`**; the obstruction is constructive.

### It is vacuous exactly where it must be

At `A = N`, `tau_A = d` and `d(m)` is odd **exactly when `m` is a perfect square**. Gaps
between squares grow like `2 sqrt(m)`, so `Odd_A` is not syndetic and the obstruction says
nothing. It had better not: Erdos carried the construction out for this `A` in 1948. A
proposed obstruction that killed the one case known to work would be refuted on sight, and
this one passes that test.

### An infinite family of support sets killed, with an exact formula

Take `A = {p, p^2, p^3, ...}` for a prime `p`, so `tau_A = v_p`. Then `v_p(m) = 1` exactly
when `p | m` and `p^2 !| m`, which happens at `p, 2p, ..., (p-1)p`, then jumps to
`p^2 + p`. Every gap is `p` except that one, which is `2p`. Hence

    maxgap(Odd_A) = 2p       and       **maxrun <= 2p - 1**.

The census attains the bound at both `p` it can reach: `p = 2` gives 3, `p = 3` gives 5.
**Every geometric support set is killed, with the cap known in closed form.**

### Census: 500,000 starting points, `n <= 10^6`, exact integer arithmetic

`scripts/socket_parity_census.py`; predictions and falsifier written into the docstring
**before** the run. Falsifier: any cohort, real or control, with
`maxrun > maxgap(Odd_A) - 1`. It **survived** in all ten rows.

| `A` | maxrun | at `N` | `maxgap(Odd_A)` | bound | control run |
|---|---|---|---|---|---|
| `N` (`tau_A = d`) | 5 | 8851 | 1999 | loose | 6 |
| primes (`omega`) | 2 | 208 | 20 | loose | 2 |
| `{2^i}` (`v_2`) | **3** | 14 | **4** | **TIGHT** | 17 |
| `{3^i}` (`v_3`) | **5** | 6558 | **6** | **TIGHT** | 31 |
| `3N` | 8 | 62994 | 3459 | loose | 33 |

Reading every row:

1. **The two geometric cohorts saturate the bound exactly** -- `3 = 4-1`, `5 = 6-1` --
   and both were unchanged from a 60,000-point pilot. There the obstruction is not an
   upper bound, it is the answer.
2. **Where the obstruction is loose, the real sequence matches its own shuffle**:
   naturals 5 against control 6, primes 2 against control 2, with argmax `N` identical in
   the pilot and the wide run. Where it is tight, shuffling explodes the run (3 to 17,
   5 to 31) -- the control makes the obstruction visible by removing it.
   **[CORRECTED, section 60: the 31 is a ZERO-RUN. A control that destroys the odd-set
   arrangement exactly as this one does but PINS the zeros gives 6, not 31.]**
3. **`3N` is an unexplained residual and I am not going to dress it up.** Its parity gap
   is 3459, so the obstruction permits runs into the thousands, yet the real maxrun is 8
   against a control of 33.
   **[RETRACTED, section 60: nothing else suppresses them. The zero-pinned control gives
   10 against the observed 8. The "something else" was zero density.]**
   **The parity obstruction
   is not the whole story**, and naming what governs `3N` is open.

**A prediction I got wrong.** I predicted `maxgap(Odd_primes) <= 8`; it is **20**. The
parity structure of `omega` is looser than I guessed, so the obstruction is weaker at the
primes than I expected -- which cuts *against* my own thesis, not for it.

### T12 discipline: the `naturals` row is not a cap

`maxrun = 5` at `A = N` over 500,000 starting points, while **Erdos proved the runs are
unbounded there**. The 5 is a search-window artifact: `2^k | d(N+k)` needs
`d(N+k) >= 2^k`, and `d <= 240` for `n <= 10^6`, so `k <= 7` is arithmetically impossible
to exceed in this range. Erdos's own construction needs `N` past a primorial tower.
**Finite search never refutes existence** (T12). Only the *syndetic* rows are caps, and
they are caps because of the theorem, not because of the search.

### Verdict

**One-way result: a complete obstruction class for the socket mechanism, stated as a
property of `A` alone.** `Odd_A` syndetic kills it; every geometric support set is killed
with cap `2p - 1`.

**What this does NOT show.** It does not decide Erdos 257, and it does not kill the socket
lane in general -- at `A = N` and at the primes the obstruction is vacuous, and those are
the cases that matter most. It gives a necessary condition (`Odd_A` has unbounded gaps),
not a sufficient one: `3N` satisfies the necessary condition and still shows short runs.
**The converse is false**, and the gap between the two is where the remaining work is.

**Nonclaim.** No unconditional progress on 257. Two mechanisms are now mapped -- one
eliminated outright (section 45), one obstructed on a describable class -- and the
frontier is the complement of that class.

## 47. The SEARCH-DEPTH LAW -- and a correction to how I framed it

I set out to add a second kill criterion beside section 46's parity obstruction. **It is
not a kill criterion, and calling it one would have been an error.** What it is turns out
to be more useful.

### The magnitude bound

Inside a socket run, `2^k | tau_A(N+k)`. A nonzero natural divisible by `2^k` is at least
`2^k`; zero coefficients are exempt, since zero is divisible by everything. Let
`a = min A`. Any `a` consecutive integers contain a multiple of `a`, so the top `a` of the
window carries some index `k >= K - a + 1` with `tau_A(N+k) >= 1`. Hence

    2^(K - a + 1)  <=  max_{m <= N+K} tau_A(m).

### Why it is not a cap

**Section 44 proved `tau_A` is unbounded for every infinite `A`.** So the right-hand side
diverges, and no `K` is ever excluded outright. The inequality does not bound the run --
it prices it. To see a run of length `K` you must search out to where `tau_A` first reaches
`2^(K-a+1)`.

| | parity (s46) | magnitude (here) |
|---|---|---|
| character | structural | quantitative |
| scope | **absolute** -- bounds the run for ALL `N`, forever | **range-bound** -- recedes as the window grows |
| status | a genuine kill criterion | a search-depth law |

That distinction is the section. Conflating the two would have converted a statement about
my telescope into a statement about the sky.

### The `3N` residual from section 46 is resolved

Section 46 recorded `3N` as unexplained: parity permits runs of 3458, observed was 8.
Magnitude gives **9**. That is the missing constraint, and the binding column now accounts
for every row.

| `A` | run | parity `<=` | magnitude `<=` | binding | `max tau_A` |
|---|---|---|---|---|---|
| `N` | 5 | 1998 | **7** | magnitude | 240 |
| primes | 2 | 19 | **3** | magnitude | 7 |
| `{2^i}` | **3** | **3** | 5 | **parity**, tight | 19 |
| `{3^i}` | **5** | **5** | **5** | **both**, tight | 12 |
| `3N` | 8 | 3458 | **9** | magnitude | 192 |

`n <= 10^6`, `N <= 5*10^5`, exact integer arithmetic, falsifier
(`run <= min(parity, magnitude)`) **survived every row**. Every prediction in the script
docstring held this time, including the four `max tau_A` values -- 240, 7, 19, 12 --
written down before the run.

### The bound is binding at the observed optima, position by position

Re-derived from scratch rather than read off the census:

- `N = 8851`, `A = N`: `d(N+k) = 6, 8, 8, 16, 32` for `k = 1..5`. The requirement is
  `2^k`, i.e. `2, 4, 8, 16, 32`. **The last three saturate exactly.** `k = 6` needs 64 and
  gets 4.
- `N = 208`, primes: `omega(N+k) = 2, 4` for `k = 1, 2`, against required `2, 4`.
  **Both exact.** `k = 3` needs `omega >= 8`, first available at 9699690.

So `N = 208` is not an accident of search: `210 = 2*3*5*7` is the smallest integer with
`omega = 4`, and the run sits precisely there.

### A quantitative separation of #69 from Erdos-Borwein, inside one mechanism

At index `k = K` the run forces `tau_A(N+K) >= 2^K` whenever that coefficient is nonzero.
For primes, `omega(m) = 0` only at `m = 1`, so a run of length `K` needs `N` past the
`2^K`-th primorial:

| `K` | needs `omega >=` | so `N >=` |
|---|---|---|
| 2 | 4 | 210 |
| 3 | 8 | 9,699,690 |
| 4 | 16 | 3.26 x 10^19 |
| 5 | 32 | 5.26 x 10^50 |
| 6 | 64 | 1.95 x 10^125 |

**Doubly exponential in `K`.** For `A = N` the same demand is `d(N+K) >= 2^K`, and since
`max d(m) = 2^((1+o(1)) log m / log log m)`, the depth is `exp(K log K)` -- **singly**
exponential, which is why Erdos's primorial-modulus construction reaches it and why he
could carry out that case in 1948.

> **The same mechanism is exponentially more expensive at the primes than at `N`.** That
> is a precise, mechanism-internal account of why #69 is harder than Erdos-Borwein, in
> place of the qualitative "multiplicativity is lost" of section 26.

### T12, made quantitative

Cross-index T12 says finite search never refutes existence. This section says how far the
search would have to go. The `naturals` row reading 5 while Erdos proved the runs
unbounded is now fully explained: `max d = 240` below `10^6` makes `k <= 7` arithmetically
unreachable, whatever the arrangement. **A census that reports a short run for a
magnitude-bound cohort has measured its own window.**

### Verdict, and what is NOT here

**One-way result:** the socket-run length is priced, and the price separates the two
classical cases exponentially. Combined with section 46, every cohort in both censuses is
now accounted for by one of two named constraints.

**Nonclaim.** No progress on 257. Magnitude kills nothing; parity kills only syndetic
`Odd_A`; and `A = N` and the primes -- the two cases that matter -- escape both. The
frontier is unchanged in extent, only better priced.

**Formalisation deferred, and not claimed.** The Lean statements
(`socketRun_forces_pow_le_coeff`, `socketRun_forces_pow_le_of_le`) were written and the
build returned **`rc = 75`, a refusal, not a failure** -- `validation_capacity_deferred`,
conflict key `lean-project-build`, ticket `rct_10e73bff34b5b6988aac`, a sibling holding
the project lease. The working tree was reverted to `HEAD`, the splice saved, and this
section claims **no machine-checked status** for the magnitude bound. It is elementary
(`Nat.le_of_dvd`), but elementary is not checked.

## 48. The kill/escape dichotomy as a GROWTH LAW -- and a circular formula, reported not used

Three things this iteration: the deferred Lean landed, my planned target turned out to be
circular, and the useful measurement was a different one.

### The magnitude bound is now machine-checked

`80270fb192` closes `cap_quick_erdos257_land_the_magnitude_bound_lean_t_936d7492719d`.
`socketRun_forces_pow_le_coeff` -- a positive coefficient inside a socket run is at least
`2^k` -- carries axioms **`[propext]` alone**. Section 47 stated this as unverified; it may
now be cited as checked. The earlier `rc = 75` was a refusal under ticket
`rct_10e73bff34b5b6988aac`; the splice was replayed from disk unchanged.

### The divisor-involution formula is TRUE and CIRCULAR

The involution `d -> m/d` on divisors of `m` has 2-element orbits plus the fixed point
`sqrt(m)` on squares. The set `{d | m : d in A and m/d in A}` is invariant, so its size is
even except at that fixed point. Hence, with
`asym_A(m) := #{d | m : d in A and m/d NOT in A}`,

    tau_A(m)  ==  asym_A(m) + [m square] * 1_A(sqrt m)     (mod 2).

Verified computationally with **zero failures** in every cohort. At `A = N` no divisor pair
is asymmetric, so `tau_A(m) == [m square]` -- the classical "`d(m)` odd iff `m` is a
square", recovered exactly, which is the check that the derivation is right.

**And it is useless as a criterion.** Off the squares the identity says `tau_A(m)` is odd
exactly when `asym_A(m)` is odd. So the criterion I intended to test -- "`Odd_A` is
syndetic iff `asym_A` is odd with positive frequency" -- reads "`Odd_A` is syndetic iff
`Odd_A` is syndetic". A true identity, a circular test. Recorded so the next actor does
not spend an iteration rediscovering that.

### What the scaling actually decides

Every earlier measurement reported `maxgap(Odd_A)` at a single `M`, and a single value
cannot separate "bounded" from "growing slowly". The verdict is the **growth law**.
`scripts/odd_gap_scaling.py`, four decades, exact integer arithmetic:

| `A` | `10^3` | `10^4` | `10^5` | `10^6` | closed form |
|---|---|---|---|---|---|
| `N` | 61 | 199 | 631 | 1999 | `2*floor(sqrt M) - 1`, **exact at all four** |
| `3N` | 105 | 339 | 1089 | 3459 | `3*(2s+1)`, `s` the last `3(s+1)^2 <= M`, **exact at all four** |
| `{2^i}` | 4 | 4 | 4 | 4 | `2p = 4`, **flat** |
| `{3^i}` | 6 | 6 | 6 | 6 | `2p = 6`, **flat** |
| primes | 9 | 11 | 20 | 20 | none known |

The two geometric rows are flat across four decades, confirming section 46's theorem
`maxgap(Odd_{p^i}) = 2p` -- a measurement agreeing with a proof, which is the only
relationship between the two worth having. The two escape rows match closed forms exactly
at every scale, because their odd sets are `{squares}` and `{3s^2}`, whose gaps are forced.

### The primes are the only cohort with no proof either way

`Odd_primes = {m : omega(m) odd}`, so a gap of `g` is a run of `g - 1` consecutive
integers with `omega` EVEN. Therefore:

> **The parity obstruction is vacuous at the primes if and only if there exist arbitrarily
> long runs of consecutive integers with `omega` even.**

That is a statement about sign patterns of `(-1)^omega`, of Chowla flavour. **I have not
verified its status in the literature and do not claim it is open.** What is recorded here
is the reduction, and the reduction is exact.

**The stall at 20 is not evidence.** The primes gap did not grow between `10^5` and `10^6`.
Under the random model a run of length `>= 21` has probability `2^-21` per position, so the
expected count over the new decade is `9 * 10^5 * 2^-21 = 0.43` -- **not seeing one is the
likely outcome**, and reading the stall as boundedness would be exactly the error of taking
a scalar at one `M` for a limit.

**A prediction I got wrong.** I predicted the primes gap would reach 14-17 by `10^4`; it is
**11**. The growth is slower than the random model at small `M`, and I said otherwise.

### Verdict

**One-way result:** the kill/escape dichotomy of section 46 is now established as a growth
law rather than a single-scale reading, with the geometric kill confirmed flat over four
decades and the two escaping cohorts matched to exact closed forms.

**What this does NOT show.** Nothing about 257. The primes -- the case that matters for
#69 -- remain undecided by this test, and their verdict is equivalent to a Chowla-type
statement I have not settled. And the involution formula, which was this iteration's
intended contribution, contributes nothing.

## 49. The two lanes do NOT converge at the primes -- and section 27 is sharpened, not contradicted

I hypothesised that at `A = primes` the transplant lane and the socket lane bottom out in
the same Dickson / Hardy-Littlewood tuples conjecture, which would have explained why #69
resists two structurally different attacks for one reason. **The hypothesis is refuted.**
The refutation is elementary, and it identifies the correct conjecture class for each lane.

### The construction I proposed is false for `K >= 4`

Proposed: distinct primes `p_1..p_K` all `> K`; by CRT pick `m` with
`m == -j + p_j (mod p_j^2)`, so `p_j || m+j`; then require each `(m+j)/p_j` prime, giving
`omega(m+j) = 2` throughout, with the `K` cofactors linear in the CRT parameter -- a
Dickson instance.

It forces every `m+j` to be a product of exactly two primes **each to the first power**.
If `4 | m+j` then, `p_j` being odd, `4 | (m+j)/p_j`, so that cofactor is not prime. One of
any four consecutive integers is `== 0 (mod 4)`. **So `K <= 3`.** Measured: the longest run
of consecutive squarefree semiprimes up to `10^6` is **exactly 3, starting at 33**
(`33 = 3*11`, `34 = 2*17`, `35 = 5*7`) -- the theorem and the data agreeing at the same
integer.

### The obvious repair is capped too

`omega` ignores multiplicity, so a run can pass a multiple of 4: `36 = 2^2 * 3^2` has
`omega = 2`, making `33..36` four consecutive `omega = 2` integers. Dropping squarefreeness
gives a longer route -- but not an unbounded one:

- **Unconditional cap 29.** Any 30 consecutive integers contain a multiple of
  `30 = 2*3*5`, which has `omega >= 3`.
- **Sparsity past length 6.** Any 6 consecutive integers contain a multiple of 6, and
  `omega = 2` there forces `2, 3 | n` with no third prime, i.e. `n = 2^a 3^b`, a 3-SMOOTH
  number. Those number `O(log^2 x)` up to `x`.

Measured to `10^6`: max `omega = 2` run is **8, starting at 141**, and there are only
**five** runs of length `>= 6` in the entire range --

| start | length | 3-smooth multiple of 6 straddled |
|---|---|---|
| 91 | 6 | `96 = 2^5 * 3` |
| 141 | 8 | `144 = 2^4 * 3^2` |
| 212 | 8 | `216 = 2^3 * 3^3` |
| 323 | 7 | `324 = 2^2 * 3^4` |
| 2302 | 7 | `2304 = 2^8 * 3^2` |

**Every one straddles a 3-smooth multiple of 6, and past 2302 there are none at all.** The
sparsity argument is confirmed with a 100% hit rate and a visible extinction point.

### Long `omega`-even runs require `omega` to VARY

The longest `omega`-even run to `10^6` is **19, starting at 38404**, matching section 48's
`maxgap(Odd_primes) = 20` exactly (a gap of `g` is a run of `g-1`). Its `omega` values are

    2 2 4 2 2 4 4 2 4 2 2 4 2 2 4 2 4 2 2      -- twelve 2s and seven 4s, NOT constant.

So the long runs are not any fixed-`omega` phenomenon. They mix `omega = 2` and
`omega = 4`, and no CRT-plus-primality construction produces that: **a tuples hypothesis
delivers primes at designated linear forms and says nothing about the remaining
factorisation of each `m+j`, which is exactly what `omega(m+j)` even constrains.**

### Verdict: the lanes need DIFFERENT conjectures

> **Pratt's lane needs a TUPLES hypothesis** -- simultaneous primality of linear forms.
> **The socket lane's parity precondition at the primes needs a CHOWLA-type hypothesis** --
> sign patterns of the multiplicative function `(-1)^omega` along consecutive shifts.

Those are different conjectures, and the reduction of one to the other does not go through.
**Section 27's incomparability therefore persists at the primes**, now at the sharper level
of which conjecture each lane consumes rather than merely of which conclusion each reaches.

### Calibration, and what I got wrong

`A = N` in the same run: `d(m)` is even iff `m` is not a square, so `d`-even runs are the
gaps between consecutive squares -- **1998** at `10^6`, against 19 at the primes. Erdos
1948 lives in that row, and the two-order-of-magnitude gap is the whole difficulty.

**A prediction I got wrong.** I predicted the maximum `omega = 2` run would be 4-7; it is
**8**. The structural prediction that accompanied it -- that every run of length `>= 6`
straddles a 3-smooth multiple of 6 -- held on all five instances.

### Nonclaim

Nothing here decides 257, and nothing here decides #69. This is the elimination of a
proposed BRIDGE between two lanes, not progress along either. The socket lane at the primes
remains undecided, and its precondition is now identified as Chowla-type rather than
tuples-type -- a sharper statement of the same open question, not an answer to it.

## 50. There is no geometric hard core -- my premise was refuted by this file's own section 7

I set out to name the "hard core": support sets where both mechanisms I had been mapping
are dead. `A = {2^j}` was the candidate, since the block engine caps at `K = 1` (section
45's census) and the socket mechanism at `K = 3` (section 46's `2p - 1`). **The premise is
false, and the refutation was already in this document.**

### `hclose` decides `A = {2^j}`

Section 7 of this file already records it, and the number checks exactly. With
`excess(N) = sum_{a in A} 2^(-delta_a(N))`, `delta_a(N) = a - (N mod a)`, and the term
vanishing exactly when `a | N`: at `N = 64` every `a in {2,4,8,16,32,64}` divides `N`, so
the first surviving term is `a = 128` with `delta = 64`, giving

    excess(64) = 2^-64 = 5.421010862427522e-20,

matching section 9 / section 23's recorded `5.42e-20`, and decaying like `2^-N` along
`N = lcm`. **So the geometric sets are not a hard core at all.** They are decided -- just
not by either lane I had been mapping.

### The solved inventory is larger than the two lanes I was working in

Section 7 already carries the exhaustion map's split plus a third class:

    (i)   A eventually periodic        -> Lambert over arithmetic progressions
    (ii)  A base-adapted, Y_A Mahler   -> Nishioka
    (iii) A reciprocal-summable        -> machine-checked,
          irrational_erdosSupportSeries_two_of_summable_reciprocal

plus `hclose` deciding particular sets such as `{2^j}`. Sections 45-49 were conducted
inside a two-lane frame that this file's own section 7 already knew to be incomplete.
**That is a navigation failure on my part, not a mathematical one**: the material was in
the file I have been appending to all session.

### Section 46's `p = 2` case was prior art in this same file

Section 7's neighbourhood already proves the transplant is empty at `K = 4` for
`A = {2^j}`, by an exact 2-adic argument: if `v_2(N+1) >= 2` then `N+1 = 4u`, so
`N+3 = 4u+2` has `v_2` **exactly 1**, while `k = 3` demands `8 | v_2(N+3)`. Two positions
two apart cannot both carry high `v_2`.

That is the same bound section 46 reports as `2p - 1 = 3` at `p = 2`. **The `p = 2`
instance is not mine.** What section 46 adds is the *criterion* -- `maxrun <= maxgap(Odd_A)
- 1`, so syndetic `Odd_A` kills the mechanism for ANY support set, with the geometric
family a corollary carrying the closed form `2p - 1`. The generalisation stands; the
instance was already on record and T25 should have cited it.

### What sections 45-49 actually contribute to the map

The exhaustion map's OPEN class is "aperiodic and not base-adapted for any `k`". Sections
46-47 refine it with a condition the map does not carry:

> For the Erdos-1948 socket route to be **available** at all, `Odd_A = {m : tau_A(m) odd}`
> must have unbounded gaps. Syndetic `Odd_A` removes the route absolutely, independently of
> periodicity, base-adaptation, and summability.

That is a fourth, orthogonal coordinate on the map, and it is the one genuinely new thing
this arc produced.

### A label I got wrong, caught by reading the row

The verification printout listed `2048, 4096, 8192` among the `a` dividing 64. They do not
divide 64: their terms are `2^-1984` and smaller, which **underflowed to `0.0`** and were
swept into the "term vanishes" bucket. The excess total is unaffected -- those terms are
negligible by construction -- but the label was false. **Third time float underflow has
produced a wrong label in this programme** (see section 23, section 24). Divisibility must
be tested by `N % a == 0`, never by "the term is zero".

### Verdict

**Negative iteration, reported as negative.** The target class does not exist; the
candidate is decided; the sub-result I thought was new at `p = 2` was already here; and the
frame I was working in was narrower than this file's own section 7. The one durable
contribution of sections 45-49 to the exhaustion map is the parity coordinate above.

**Nonclaim.** Nothing here advances 257. Locating the open class more precisely is not
progress toward the proof, and this iteration did not even do that -- it corrected my
account of where the open class is.

## 51. The parity map is a BIJECTION -- and the parity coordinate is NOT vacuous on the open class

Section 50 left one question that decides how much section 46 is worth: on the class where
Erdos 257 is actually open -- `sum_{a in A} 1/a = infinity`, since reciprocal-summable is
solved -- can `Odd_A` be syndetic at all? If divergence forced unbounded gaps, the parity
obstruction would never bite where the problem lives. **It does not force it, and there is
an explicit witness.**

### The parity map `A -> Odd_A` is a bijection over `F_2`

`tau_A = 1_A * 1` in Dirichlet convolution. Over `F_2`, convolution by the constant-one
function is invertible, with inverse convolution by `mu`, and `mu(n) == 1 (mod 2)` exactly
when `n` is squarefree. Hence

    1_A(n)  ==  sum_{d | n, n/d squarefree} tau_A(d)     (mod 2).

**For any target set `S` there is exactly one `A` with `Odd_A = S`.** The parity coordinate
therefore constrains nothing about `A` on its own -- it is a reparametrisation, not a
filter. Verified by two independent exact calibrators, both landing on the nose:

| target `S` | must return | returned |
|---|---|---|
| `{perfect squares}` | `A = N` | `A = N` |
| `{m : v_2(m) odd}` | `A = {2,4,8,16,...}` | `A = {2,4,8,16,...}` |

with round-trip exact on every target: recomputing `tau_A` from the derived `A` reproduces
`S` on the whole range.

### A prediction I got badly wrong

I predicted the `A` realising `S = 2N` would have positive density. **It is the singleton
`A = {2}`** -- obviously so in hindsight, since `tau_{{2}}(m) = [2 | m]`. Likewise
`S = 3N` gives `{3}` and `S = N` gives `{1}`. Finite unions of arithmetic progressions come
from FINITE `A`, which Erdos 257 does not even quantify over. My prediction was not
slightly off; it was the wrong order of magnitude and the wrong kind of object.

### The witness: `A = N \ {2^i}`

`Odd_A` is XOR-linear in `A`, so subtracting the powers of two from `N` subtracts their odd
sets. With `v = v_2(m)` and `u` the odd part,

    tau_A(m) = d(m) - v_2(m),   d(m) = (v+1) d(u).

At `m == 2 (mod 4)`: `v = 1`, so `d(m) = 2 d(u)` is EVEN and `tau_A(m) = even - 1` is
**odd**. Every such `m` lies in `Odd_A`, for every `m`. Hence `maxgap(Odd_A) <= 4`.
Measured to `3 x 10^5`: **max gap exactly 4**, density `0.335`, and the `m == 2 (mod 4)`
clause verified at every point.

| property | value |
|---|---|
| infinite | yes |
| `sum_{a in A} 1/a` | **diverges** -- only a convergent geometric series is removed from the harmonic series |
| `Odd_A` syndetic | **yes, gap 4** |
| eventually periodic | **no** -- `1_A` vanishes only at the `2^i`, whose gaps grow without bound, so no fixed period survives past `2^i > r` |

**So the parity obstruction is non-vacuous exactly where Erdos 257 is open.** Section 50's
T29c stands, and is sharpened rather than deflated: syndetic `Odd_A` is compatible with
divergence and aperiodicity, so the fourth coordinate cuts the open region rather than
grazing it.

### And this is the hard-core candidate section 50 failed to find

Section 50 hunted sets where the mapped mechanisms die and found none, because the
geometric candidates are decided by `hclose`. `A = N \ {2^i}` is a better candidate:

* **not class (i)** -- aperiodic, shown above;
* **not class (iii)** -- reciprocal sum diverges;
* **socket / Erdos-1948 route DEAD** -- `Odd_A` syndetic with gap 4 forces
  `maxrun <= 3`, by section 46.

**What is NOT tested, and must not be glossed:** class (ii), base-adaptation -- whether
`Y_A` satisfies a Mahler equation for some `k` -- is untested here, and section AN's
nullity machinery is the instrument for it. `hclose` at this `A` is also untested; section
50's whole lesson was that `hclose` decides sets the mechanism census had written off.
**Until both are checked this is a candidate, not the hard core**, and calling it more
would repeat exactly the error section 50 corrected.

### Nonclaim

Nothing here advances 257. One coordinate of the exhaustion map is shown to cut the open
region, and one explicit set is proposed for the two tests that would decide whether it
sits in the open region at all.

## 52. The candidate DIES on base-adaptation -- and the whole construction strategy dies with it

Section 51 proposed `A = N \ {2^i}` as an open-class candidate and flagged two untested
gates. Both are now tested. It passes one and **fails the other**, and the failure
generalises to kill the construction method that produced it.

### Gate (a), `hclose`: FAILS, so the candidate survives this one

`excess(N) = sum_{a in A} 2^(-(a - N mod a))`, term zero exactly when `a | N`. For
`A = N \ {2^i}` and `N + 1` not a power of two, `N+1 in A` and `delta_{N+1}(N) = 1`, so
`excess(N) >= 1/2`; when `N + 1 = 2^i` the terms at `N+2, N+3, ...` supply
`1/4 + 1/8 + ... = 1/2` less a negligible correction. Measured over 70 values of `N`
including every `2^i - 1` up to `2^11` and every `lcm(1..k)` to `k = 11`:

    min excess = 0.367157 at N = 1,  and the values GROW with N
    [RETRACTED, s57/T36a: 0.367157 is an APPROXIMATION artefact and is TOO HIGH.
     The exact minimum for THIS support is 0.202758 at N = 1 (s64).
     [T36a originally recorded 0.206435 here; that is the A* value, and s64 proved
      it does NOT belong to this section's A.  T36a is corrected at source.]
     The VERDICT survives -- the question was whether the minimum is bounded away
     from zero. See s63 residual (u): T36a assigns ONE exact value to TWO DIFFERENT
     supports (this section's A and section 55's A*), which is UNVERIFIED.]
    (lcm rows: N=6 -> 0.812, N=60 -> 1.653, N=420 -> 1.984, N=2520 -> 2.950)

**Correction to my own derivation:** I claimed `excess >= 1/2` for all `N`. That holds for
`N >= 4`; the two smallest cases `N = 1` and `N = 3` give `0.367` and `0.469`. The
**[RETRACTED FIGURES, s57/T36a -- the `N >= 4` restriction is CORRECT and stands; only
the two printed numbers are approximation artefacts. See the note above.]** The
substance is unaffected -- `liminf excess > 0`, so `hclose` does not decide this `A`.

### Gate (b), base-adaptation: the candidate DIES

`Y_A(x) = sum_n 1_A(n) x^n = x/(1-x) - f(x)` with `f(x) = sum_{i>=1} x^(2^i)`, and
`f(x^2) = sum_{i>=2} x^(2^i) = f(x) - x^2`. Hence

    Y_A(x) - Y_A(x^2) = x/(1-x) - x^2/(1-x^2) - x^2 = x/(1-x^2) - x^2,

and clearing the denominator gives an exact order-one Mahler relation at `k = 2`:

    (1 - x^2) Y_A(x)  -  (1 - x^2) Y_A(x^2)  =  x - x^2 + x^4,

every degree at most 4, comfortably inside the `(d = 2, D = 5)` box. The corpus's own
instrument `scripts/mahler_nullity_independent.py` confirms it:

| sequence | k=2 | k=3 | k=4 |
|---|---|---|---|
| `{2^(2^k)}` (section AN calibrator) | 0 | 0 | 0 |
| `N` (control -- must fire) | 14 | 9 | 8 |
| **`N \ {2^i}` (the candidate)** | **8** | 0 | 2 |

The calibrator reproduces section AN exactly and the control fires, so the instrument is
reading correctly. **`A = N \ {2^i}` is base-adapted at `k = 2`, hence class (ii), hence
SOLVED by Nishioka. It is not in the open class.**

### The general obstruction: XOR from adapted pieces can never escape class (ii)

`Y_A` is ADDITIVE in `A` -- `Y_{A xor B} = Y_A + Y_B - 2 Y_{A and B}`, and for disjoint or
nested sets simply a difference. So a Mahler relation for `Y_A` and one for `Y_B` combine
into one for the symmetric difference. The instrument's own control table shows both my
ingredients are adapted at `k = 2`: `N` at nullity 14, `{2^i}` at nullity 12. Their
difference had to be adapted, and it is.

> **Section 51's `F_2`-linear construction cannot reach the open class from adapted
> ingredients.** The XOR-linearity that made a syndetic `Odd_A` easy to build is exactly
> what preserves base-adaptation. Any future candidate must contain a genuinely
> NON-adapted ingredient, not merely a sparse one.

That is the durable finding of this iteration, and it is a constraint on method rather than
a result about `257`.

### The primes are still the canonical open instance

Same instrument, same run: `primes` gives nullity `0, 0, 0` -- not base-adapted in this
box, matching their status as aperiodic, reciprocal-divergent, and undecided. Everything
landed remains consistent with the primes being where the difficulty actually sits.

**Parameter box, stated honestly:** nullity `0` at `(d = 2, D = 5)` rules out relations
**in that box only**. It is not a proof that no Mahler relation exists at any order or
degree, and neither the primes row nor the `2^(2^k)` calibrator should ever be quoted as
one.

### Nonclaim

Nothing here advances 257. One named candidate is eliminated, one construction strategy is
shown to be structurally incapable of producing candidates, and the honest position is that
**I currently have no explicit member of the open class.**

## 53. Correcting section 52, and the DUAL of T31a -- non-adaptation survives XOR

### The correction I owe section 52

Section 52 closed: *"I currently have no explicit member of the open class."* **That is
wrong.** The exhaustion map's OPEN class is "aperiodic and not base-adapted", and the
primes are aperiodic, have `sum 1/p = infinity` (so not class iii), and read nullity
`0,0,0` (so not base-adapted in the box). **The primes satisfy every coordinate; they ARE
an explicit named member, and the corpus has always known it** -- they are Erdos #69.

What I actually lacked was a member OTHER than the primes. The overstatement came from
reading my own failed constructions as an absence rather than as a failure to add to
something already present.

### The dual of T31a: non-adaptation SURVIVES xor with adapted material

T31a says XOR from adapted pieces can never escape class (ii). The dual is what makes
construction possible at all. Mahler-adapted functions at fixed `k` form a MODULE --
relations for `Y_1` and `Y_2` combine into one for `Y_1 +- Y_2` at higher order. So if `B`
is adapted at `k` and `P xor B` were adapted at `k`, then `P = (P xor B) xor B` would be
adapted. Contrapositive:

> **`P` not adapted at `k`  =>  `P xor B` not adapted at `k`, for every adapted `B`.**

**Confirmed with the instrument doing visible work:** `3N` is periodic, hence adapted, and
FIRES at nullity `6, 3, 3`. Yet `primes xor 3N` reads `0, 0, 0`. The adapted ingredient did
not contaminate the non-adapted one, exactly as the module argument requires.

### Five explicit open-class members other than the primes

`scripts/open_class_member_search.py`, `n <= 10^5`, nullity box `(d = 2, D = 5)`,
calibrators passing (`N` fires `14,9,8`; `primes` reads `0,0,0`):

| `A` | nullity `k=2,3,4` | `sum 1/a` partial | `Odd_A` gaps `10^3/10^4/10^5` |
|---|---|---|---|
| `primes xor {2^i}` | `0,0,0` | 2.705 | 10, 12, 18 |
| `primes xor 3N` | `0,0,0` | **5.702** | 12, 12, 20 |
| `primes xor {n^2}` | `0,0,0` | 4.347 | 10, 13, 17 |
| `primes xor {2^(2^k)}` | `0,0,0` | 2.522 | 10, 19, 19 |
| `primes minus {p == 1 mod 4}` | `0,0,0` | 1.770 | 8, 8, 11 |

Each is aperiodic, reciprocal-divergent (`primes minus {p == 1 mod 4}` by Dirichlet, the
rest because the primes' divergence survives a summable or divergent perturbation), and
box-non-adapted at `k = 2, 3, 4`.

**The uncertain row resolved the same way.** `primes xor {2^(2^k)}` XORs two NON-adapted
ingredients, where no theorem applies in either direction. It reads `0,0,0` as well --
worth recording precisely because it was not predictable.

### Coordinate (4) fails everywhere, as predicted

`Odd_A` gaps GROW with `M` for every candidate -- measured across three decades, never at
one `M` (T27a). So the section-46 parity obstruction does **not** bite on any of them, and
the socket route stays formally available. I predicted this before the run and it held.

### How much are these worth? Less than they look

They are genuine members, and their irrationality is not reducible to #69 -- a sum plus a
decided piece can be anything. But four of the five are the primes perturbed by a set whose
own status is settled, so they inherit their difficulty from the primes rather than
exhibiting a new source of it. The arithmetically most distinct is
**`primes minus {p == 1 mod 4}` = `{2} union {p == 3 mod 4}`**, a fixed-residue-class prime
set, divergent by Dirichlet, and not a perturbation-by-decided-set at all.

**Parameter box (T31c):** every `0` above rules out Mahler relations **inside
`(d=2, D=5)` at `k = 2,3,4` only**. None of these rows is a proof of non-adaptation.

### Nonclaim

Nothing here advances 257. The open class is populated rather than characterised, the
members are perturbations of the one instance that was already known, and section 52's
claim that none existed is retracted.

## 54. Coordinate (4) CLOSED -- an open-class set whose socket route is dead

Section 53 / T32c left one gap sharply posed: every set known to be in the exhaustion map's
OPEN class had `Odd_A` with GROWING gaps, so the section-46 parity obstruction never bit
where the problem is open. **That gap is now closed, by an explicit set.**

### The planned construction collapsed, which was the first thing to learn

The plan was: pick syndetic `S`, solve `Odd_B = Odd_P xor S`, set `A = P xor B`. But the
parity map is `F_2`-LINEAR, so `B = P xor C` with `Odd_C = S`, and

    A = P xor B = P xor (P xor C) = C.

**The primes cancel.** `A` is just the inverse transform of `S`, and the perturb-the-primes
framing was redundant. Worse, the obvious target is a dead end: forward `{d} -> dN`, so any
`S` that is a finite Boolean combination of APs has a FINITE preimage (T30a). Verified as
an independent check on the transform: the preimage of `{m == 2 mod 4} = 2N xor 4N` is
**exactly `{2, 4}`**.

### The mechanism, and why a `4N` perturbation preserves it

`C = N \ {2^i}` has `Odd_C` containing `{m == 2 mod 4}` for a reason worth stating: at such
`m` the ONLY power of two dividing `m` is `2` itself, so deleting `2` from the support
gives `tau_C(m) = d(m) - 1 = 2 d(u) - 1`, which is ODD. Section 52 killed that set for
being base-adapted at `k = 2` (nullity 8).

> **If `D` is contained in `4N`, no element of `D` divides any `m == 2 mod 4`, since such
> `m` are not divisible by 4. So `tau_{C xor D}(m) = tau_C(m)` there, and
> `Odd_{C xor D}` still contains `{m == 2 mod 4}` -- syndetic with gap 4, untouched.**

That is a proof, not a measurement. And if `D` is non-adapted, T32a makes `C xor D`
non-adapted, because `C` is adapted. So the perturbation must be non-adapted **and** live
inside `4N`. The candidate: `D = {4p : p prime}`.

### The witness

**`A = (N \ {2^i}) xor {4p : p prime}`**, measured to `2 x 10^5` with calibrators passing
(`N` fires `14,9,8`; `primes` reads `0,0,0`; preimage check exact):

| coordinate | requirement | measured |
|---|---|---|
| (1) not class (iii) | `sum 1/a` divergent | **11.372** and growing like `log x` |
| (2) not class (i) | aperiodic | yes -- `1_A` differs from `1_N` only on `{2^i}` and `{4p}`, whose gaps grow |
| (3) not class (ii) | nullity `0,0,0` | **`0, 0, 0`** at `k = 2,3,4` |
| (4) socket route dead | `Odd_A` syndetic | **gap exactly 4 at every scale** `10^3, 10^4, 10^5, 2x10^5` |

**This is the first set with both open-class membership and a dead socket route.**

### The contrast row proves the containment is doing the work

`(N \ {2^i}) xor primes` reads nullity `0,0,0` as well -- equally non-adapted -- but its
`Odd` gaps GROW: `10, 12, 18, 23`. The primes are not inside `4N`, so they DO divide some
`m == 2 mod 4` and break the mechanism. **Non-adaptation alone is not what closes
coordinate (4); the `4N` containment is.** The ingredient `{4p}` itself reads `0,0,0`, as
predicted, and its own `Odd` gaps grow -- irrelevant, since only the composite matters.

### What this does NOT establish

* **Non-adaptation is box-only (T31c).** `0` rules out relations inside `(d=2, D=5)` at
  `k = 2,3,4`. T32a upgrades it to genuine non-adaptation only if `{4p}` is genuinely
  non-adapted, which I have NOT proved.
* **A dead socket route is not a decided problem.** Section 46 removes one mechanism; it
  says nothing about whether `sum_{a in A} 1/(2^a - 1)` is irrational.
* **The set still inherits its difficulty.** It is `N` minus sparse structured pieces, like
  every other member in section 53. Nothing here exhibits a NEW source of difficulty.

### Nonclaim

Nothing advances 257. One coordinate of the map is shown to be simultaneously satisfiable
with the other three, by one explicit set, and the mechanism that makes it work is a
containment condition rather than anything about irrationality.

## 55. Every catalogued mechanism fails on `A*` -- with a very uneven evidence ledger

Section 54 left two gates untested on `A* = (N \ {2^i}) xor {4p : p prime}`. Both are now
run, and both die. **But the six failures are not equally well established, and section 50
corrected exactly the overreach of flattening that distinction.**

### The two new gates

**`hclose` FAILS, so it does not decide `A*`.** With
`E = {2^i : i>=1} u {4p : p odd prime}` we have `A* = N \ E`, and since `E` has density
zero, `a = N+1` lies in `A*` for almost every `N`, giving `delta = 1` and a term of `1/2`.
Measured over 70 values of `N` including every `2^i - 1` to `2^11` and every `lcm(1..k)` to
`k = 12`: **min excess `0.374` at `N = 1`**, values growing (`N = 127` gives `2.34`).
**[RETRACTED, section 57: `0.374` is an approximation artefact. The exact minimum is
`0.206435`, also at `N = 1`. See section 62 for why this stood here for seven sections.]**

**The block/transplant engine is capped at `K = 3`.** Section 47 showed the engine needs
`K -> infinity`, so any fixed cap kills it. The calibrator confirms the census is
trustworthy: `A = N` returns **`K = 2` at `N = 2`**, exactly section 45's proven value.

> **But the control reaches `K = 2`.** A marginal-preserving shuffle of `tau_{A*}` attains
> a block of length 2 at `N = 1031`, against the real sequence's 3 at `N = 6`. **That is
> barely above the coincidence null, and I will not present it as a structural
> obstruction.** Contrast the socket route, where T33b is a proof.

### The evidence ledger, which is the actual deliverable

| mechanism | verdict on `A*` | evidence class |
|---|---|---|
| (i) eventually periodic | NO -- aperiodic | **PROVEN** (`1_{A*}` differs from `1_N` only on `E`, whose gaps grow) |
| (iii) reciprocal-summable | NO -- divergent | **PROVEN** (harmonic minus a density-zero set) |
| socket / Erdos 1948 | DEAD -- `Odd_{A*}` syndetic, gap 4 | **PROVEN** (T33b containment lemma) |
| (ii) base-adapted | NO -- nullity `0,0,0` | **BOX-ONLY** -- `(d=2, D=5)` at `k=2,3,4` (T31c) |
| `hclose` | FAILS -- min excess **`0.206435`** (`0.374` RETRACTED, s57) | **MEASURED-IN-RANGE** (70 values of `N`) |
| block / transplant | **DEAD, `K = 3` only at `N = 6`** | **PROVEN** (section 56; this row said MEASURED-IN-RANGE for six sections) |

**Four PROVEN, one BOX-ONLY, one MEASURED-IN-RANGE.** That is the honest shape.
**[UPDATED, section 62: as written this row said "Three PROVEN ... two
MEASURED-IN-RANGE". Section 56 promoted the block row to a theorem and section 57
retracted the `hclose` number, and neither correction reached this table.]**

### What may and may not be said

**May be said:** `A*` is an explicit infinite set on which every mechanism this programme
has catalogued fails, and three of those failures are proofs rather than measurements.

**May NOT be said:** that `A*` is *the* hard core. Two gates rest on finite search, which
by T12 never refutes existence; one rests on a bounded parameter box; and the block row is
statistically weak against its own control. Section 50 named a hard core on thinner
evidence than this and had to retract it.

**Also may not be said:** that anything about Erdos 257 follows. Every mechanism failing on
a set is a statement about the mechanisms, not about the irrationality of
`sum_{a in A*} 1/(2^a - 1)`, which remains untouched.

### What would upgrade the ledger

The block row is the weakest. Section 45's kill at `A = N` was PROVEN by an exact
argument (`d(N+2)=3` and `d(N+3)=3` force consecutive prime squares). The analogous
argument for `A*` does not transfer verbatim -- the head values differ,
`tau_{A*}(1) = 1`, `tau_{A*}(2) = 1`, `tau_{A*}(3) = 2`, so `j = 1,2,3` demand
`tau(N+1) = 2`, `tau(N+2) = 2`, `tau(N+3) = 3` rather than section 45's clauses. Deriving
the exact cap for `A*` would move that row from MEASURED to PROVEN and is the obvious next
piece of work.

### Nonclaim

Nothing here advances 257. A set is exhibited on which the catalogued mechanisms fail, with
the evidence for each failure labelled, and two of the six labels are weak enough that the
set must be called a candidate rather than a resolution of anything.

## 56. The block cap for `A*` is PROVEN: `K = 3`, attained only at `N = 6`

T34c flagged the block row as the weakest in section 55's ledger -- capped at `K = 3` by
measurement, with a shuffled control reaching 2, so near-chance. **It is now a theorem.**

### The two structural facts

`A* = N \ E` with `E = ({2^i : i>=1} u {4p : p prime}) \ {8}`, and
`tau_{A*}(m) = d(m) - e(m)` where `e(m) = #{a | m : a in E}`.

**Fact 1. Every element of `E` is even, so `tau_{A*}(m) = d(m)` for every ODD `m`.**
Verified as an identity for all odd `m <= 4 x 10^5`.

**Fact 2. For EVEN `m`: `tau_{A*}(m) = 2` if and only if `m = 2^v` with `v >= 3`.**
Write `m = 2^v u` with `u` odd, `v >= 1`. Then `d(m) = (v+1) d(u)` and

    e(m) = (v - [v >= 3]) + [v >= 2] * omega(u),

the first term counting `2^i | m` with `1 <= i <= v` except the excluded `8`, the second
counting `4p | m` for odd primes `p` (which needs `4 | m` and `p | u`). Hence

    tau_{A*}(m) = (v+1) d(u) - v + [v >= 3] - [v >= 2] omega(u).

Setting this to `2`: `v = 1` gives `2 d(u) = 3`, impossible; `v = 2` gives
`3 d(u) - omega(u) = 4`, with no solution (`u = 1` gives 3, `u = p` gives 5, and larger
`u` only increases it); `v >= 3` gives `(v+1) d(u) - omega(u) = v + 1`, forcing `u = 1`.
So `m = 2^v`, `v >= 3`. **Verified as exact set equality to `4 x 10^5`.**

### The cap

The shift clause is `tau_{A*}(N+j) = tau_{A*}(j) + 1`, and the head values are
`tau_{A*}(1..6) = 1, 1, 2, 1, 2, 3`, so `j = 1..4` demand
`tau(N+1) = 2`, `tau(N+2) = 2`, `tau(N+3) = 3`, `tau(N+4) = 2`.

**`N` even.** Then `N+2` and `N+4` are even, and both demand `tau = 2`, so by Fact 2 both
are powers of two `>= 8`. But `2^w - 2^v = 2` forces `{2^v, 2^w} = {2, 4}`, since
`2^v + 2 = 2(2^(v-1) + 1)` has 2-adic valuation exactly 1 while `2^w` has valuation
`w >= 3`. **Contradiction, so `K <= 3`.**

**`N` odd.** Then `N+1` is even with `tau = 2`, so `N+1 = 2^v`, `v >= 3`. Now `N+2 = 2^v+1`
is odd, and Fact 1 makes `j = 2` demand `d(2^v + 1) = 2`, i.e. `2^v + 1` PRIME. And
`N+3 = 2^v + 2 = 2(2^(v-1) + 1)` has `v_2 = 1`, so `tau(N+3) = 2 d(2^(v-1)+1) - 1`, and
`j = 3` demands this equal `3`, i.e. `2^(v-1) + 1` prime as well. A number `2^t + 1` is
prime only if `t` is a power of two; `v - 1` and `v` cannot both be powers of two for
`v >= 3`. **So `K <= 2` when `N` is odd.**

### `K = 3` happens exactly once

`K = 3` needs `N` even with `N+2 = 2^v` (`v >= 3`), `N+1 = 2^v - 1` prime, and `N+3` odd
with `tau = d = 3`, i.e. `2^v + 1 = q^2` for an odd prime `q`. Then
`2^v = q^2 - 1 = (q-1)(q+1)`, so `q-1` and `q+1` are both powers of two differing by 2,
forcing `q = 3` and `v = 3`. **Hence `N = 6`, uniquely** -- which is exactly the argmax the
section-55 census reported.

> **THEOREM. For `A* = (N \ {2^i}) xor {4p : p prime}`, the maximal shifted-block length is
> `K = 3`, attained only at `N = 6`.** Section 47 requires `K -> infinity`, so the
> block/transplant engine is dead on `A*` -- **PROVEN, not measured.**

### The ledger, updated

| mechanism | verdict on `A*` | evidence |
|---|---|---|
| (i) eventually periodic | NO | PROVEN |
| (iii) reciprocal-summable | NO | PROVEN |
| socket / Erdos 1948 | DEAD | PROVEN (T33b) |
| **block / transplant** | **DEAD, `K = 3` only at `N = 6`** | **PROVEN (this section)** |
| (ii) base-adapted | NO, nullity `0,0,0` | BOX-ONLY (T31c) |
| `hclose` | FAILS, min excess **`0.206435`** (`0.374` RETRACTED, s57) | MEASURED-IN-RANGE |

**Four PROVEN, one BOX-ONLY, one MEASURED-IN-RANGE.** T34a's warning is now spent: the
block row no longer rests on a near-chance measurement, and the control is irrelevant to a
theorem.

### What is still not established

`hclose` remains a finite-range measurement, and base-adaptation remains box-only -- so
**`A*` still may not be called the hard core**, and T34b stands. Nothing here bears on
whether `sum_{a in A*} 1/(2^a - 1)` is irrational; four mechanisms provably failing on a set
is a statement about those mechanisms.

### Nonclaim

No progress on Erdos 257. One row of one ledger moved from measurement to proof.

## 57. INSTRUMENT ERROR: my excess scripts used an approximation -- the `hclose` proof, repaired

I set out to prove `excess >= 1/4` for `A*`. **The claim is false, and finding out why
exposed an error in every excess measurement this programme has recorded.**

### The error

`ReciprocalSupportIrrationality.lean:21` defines the corpus's own atom:

    shiftedMersenneAtom N d = 2^(N mod d) / (2^d - 1)      (d >= 1)

so with `y = Phi_A(0)`, the EXACT excess term at support element `a` is

    (2^(N mod a) - 1) / (2^a - 1),

which vanishes exactly when `a | N`, as required. **Every excess script I have written uses
`2^(-delta)` with `delta = a - (N mod a)` instead.** Writing `r = N mod a`, the comparison
is `(2^r - 1)/(2^a - 1)` against `2^(r-a)`, and cross-multiplying gives `-2^a` against
`-2^r`; since `r < a`, **the exact term is strictly SMALLER than the approximation.**

The two agree to high precision when `delta` is large -- section 50's `excess(64) = 2^-64`
for `A = {2^j}` is unaffected, since there the exact value is
`(2^64 - 1)/(2^128 - 1) = 2^-64` to nineteen digits. **They differ materially when `delta`
is small**, which is exactly the regime the `A*` minimum lives in: at `a = N+1` the
approximation says `1/2` while the exact term is `(2^N - 1)/(2^(N+1) - 1)`, i.e. `1/3` at
`N = 1`.

### The claim I was about to prove is FALSE

Exact computation over 67 values of `N`:

| `N` | EXACT excess | approximation | `>= 1/4`? |
|---|---|---|---|
| **1** | **0.206435** | 0.374479 | **NO** |
| 2 | 0.619304 | 0.748959 | yes |
| 3 | 0.445043 | 0.497917 | yes |
| 6 | 1.005388 | 1.045837 | yes |
| 2520 | 2.882922 | 2.883512 | yes |

`N = 1` is the sole violation, and the exact minimum over the range is **0.206435**, not
the `0.374` section 55 recorded.

### Corrections to the record

**Section 52's `min excess 0.367` and section 55's `min excess 0.374` are approximation
values and are too high.** The exact minima are lower. **Both verdicts survive** -- the
question was whether the minimum is bounded away from zero, and `0.206 > 0` -- but the
numbers as printed are wrong and should not be quoted.

### The repaired bound, and it IS a proof

**Lemma (general).** Let `E = N \ A` contain no two consecutive integers. Then for every
`N >= 1`,

    excess_A(N)  >=  (2^N - 1) / (2^(N+2) - 1).

*Proof.* `N+1` and `N+2` are consecutive, so at least one lies in `A`. Neither divides `N`,
and `N mod (N+1) = N mod (N+2) = N`. If `N+1 in A` its term is
`(2^N - 1)/(2^(N+1) - 1)`, which exceeds the stated bound; otherwise `N+2 in A` and its
term is exactly the bound. All other terms are nonnegative. QED

`A*` qualifies because `E` is entirely EVEN and consecutive integers have opposite parity.
The right side is increasing in `N`, equals `1/7` at `N = 1`, and tends to `1/4`. Hence

> **`excess_{A*}(N) > 0` for every `N >= 1`, and `liminf excess >= 1/4 > 0`, so `hclose`
> FAILS for `A*` -- PROVEN, not measured.**

Verified: no exact value violates `>= 1/7`, and `N = 1` attains `0.206`, comfortably above.

**The lemma is not about `A*`.** It kills `hclose` for EVERY support set containing all the
odd numbers, `A = N` included -- consistent with T14's independent finding there.

### The ledger

| mechanism | verdict on `A*` | evidence |
|---|---|---|
| (i) periodic | NO | PROVEN |
| (iii) reciprocal-summable | NO | PROVEN |
| socket / Erdos 1948 | DEAD | PROVEN (T33b) |
| block / transplant | DEAD, `K = 3` only at `N = 6` | PROVEN (T35) |
| **`hclose`** | **FAILS, `liminf >= 1/4`** | **PROVEN (this section)** |
| (ii) base-adapted | NO, nullity `0,0,0` | BOX-ONLY (T31c) |

**Five PROVEN, one BOX-ONLY.** The remaining row cannot be upgraded by computation: T31c
exists because absence in a parameter box is not absence, and proving `A*` admits no Mahler
relation at ANY order is research-scale. **T34b therefore still stands -- `A*` is not the
hard core.**

### Nonclaim

No progress on Erdos 257. One row moved to proof, one instrument error was found and its
consequences traced, and two previously recorded numbers are retracted.

## 58. Instrument repaired -- and section 57 said the wrong thing about WHEN it was wrong

Section 57 found that every excess script used `2^(-delta)` in place of the exact atom
term. Fixing it produced three further corrections, one of them to section 57 itself.

### The blast radius is one function, not a class

Sweeping `formal_math/erdos257_period_noncollapse/scripts/` for excess computations:
**only `witness_remaining_gates.py` computes one.** `syndetic_open_member.py` has none, and
the six other negative-power-of-two uses -- in `beta_gap_equidistribution.py`,
`cantor_staircase_run_length_lab.py`, `close_return_criterion_boundary.py`,
`density_complexity_transition.py`, `exhaustive_deep_death_hunt.py`,
`gap_equidistribution_independent.py` -- are epsilon thresholds and geometric predictions.
**Legitimate, and untouched.**

**My first sweep pattern missed my own offender.** I grepped `2\.0\*\*-`; the code reads
`2.0 ** -d`, with spaces. Nothing matched in the file I already knew was wrong. **Grep
proves existence, never absence** -- a pattern that finds nothing has told you about the
pattern.

### Section 57's characterisation was wrong: the error is governed by `r`, not `delta`

Section 57 said exact and approximate "agree at large `delta`". **False.** Writing
`r = N mod a`,

    atom_exact / atom_approx = (2^a - 2^(a-r)) / (2^a - 1)  ->  1 - 2^(-r),

which depends on `r` alone. Measured:

| `r` | `a` | `delta` | ratio |
|---|---|---|---|
| 1 | 200 | 199 | **0.5000000000** |
| 1 | 5000 | 4999 | **0.5000000000** |
| 2 | 300 | 298 | 0.7500000000 |
| 64 | 128 | 64 | 1.0000000000 |

**At `r = 1` the two differ by a factor of two however large `delta` is.** Section 50's
`excess(64) = 2^-64` survives because there `r = 64`, not because `delta` was large -- I
conflated the two because both were large in that one instance.

### The guard, and its first run failing

`atom_exact` and `atom_approx` are now both present, the second only so a guard can
demonstrate the defect, and `_guard()` runs at import so **every execution exercises it**.
It asserts: at `r = 1` the two must DISAGREE with ratio approaching `1/2`; at `r = 64` they
must agree to `2^-60`; and beyond the skip threshold both must vanish together.

**Its first run failed** -- I had asserted strict inequality at `a = 5000`, where both terms
are legitimately skipped as negligible, so the assertion compared two zeros. That is the
guard catching a bug in the guard, which is the only kind of first run worth having.
Restructured: the ratio law is tested inside the evaluated regime, skip symmetry outside it.

### Re-run: no verdict changed

| quantity | before (approx) | after (exact) |
|---|---|---|
| `A*` `hclose` min excess | 0.374 (RETRACTED) | **0.206435 at `N = 1`** |
| `A*` block cap | `K = 3` at `N = 6` | `K = 3` at `N = 6` |
| calibrator `A = N` block | `K = 2` at `N = 2` | `K = 2` at `N = 2` |

The exact minima now match section 57's independent hand computation to six places.
**Expectation confirmed rather than assumed:** section 57 predicted no verdict would
change, and none did.

### `scoped_commit` `rc = 2` has a THIRD cause

The commit returned `rc = 2` twice. My standing rule says `rc = 2` is either a real claim
collision or a transient `head_cas` race, distinguished by retrying once -- a race succeeds,
a collision repeats. It repeated, so I read the payload rather than concluding:

    exact paths do not resolve to one active owner session;
    uncovered_paths=['state/.../witness_remaining_gates_receipt.json']

**Neither cause. The preflight claimed the script but not the receipt**, so the path set had
no single owner. **`rc = 2` third meaning: INCOMPLETE PATH CLAIM.** Re-preflighting both
paths gave `rc = 0` immediately. Retrying twice would never have fixed it; reading the
message did.

### Nonclaim

No mathematics here. One instrument is correct, one guard pins the defect on every run,
section 57's account of the error is corrected, and a third exit-code meaning is recorded.

## 59. The third-adaptation question: prior art answered it, and the gate extends by two operators

The exhaustion map's section AP asks whether a THIRD adaptation exists with positive
density -- a class adapted to some semigroup action other than `+ mod r` or `* k`. **I had
never attacked it. It turns out I had, and forgot.**

### Prior art, read before deriving anything

`AffineAdaptationBreadthGate.md` -- in my own directory -- already disposes of exactly the
three candidates section AP names:

* **translated affine `n -> an+b`, `b != 0`:** incompatible with a fixed finite Mahler
  tower at the Lambert-kernel level. `K_(an+b)` has poles at primitive `(an+b)`-th roots of
  unity; a tower `K_n(x), K_n(x^a), ..., K_n(x^(a^J))` has poles only at orders dividing
  some `a^j n`. Choose `n` coprime to `b` with `an+b > a^J`; then `gcd(n, an+b) = 1`, so
  `an+b` divides no `a^j n`, and polynomial coefficients cannot manufacture the missing
  primitive pole.
* **finite affine-orbit support:** `u_(t+1) = a u_t + b` gives `u_t >= a^t u_0`, so
  `sum_t 1/u_t <= a/((a-1) u_0) < infinity` -- reciprocal-summable, hence class (iii), and
  `O(s log X)` elements through `X` cannot be positive density.
* **finite `k`-adic substitution:** still the action `x -> x^a`; a renamed multiplication.

**Reading that file first was the whole iteration.** T29a exists because I once appended
six sections to a document whose own section 7 answered the question; this is the same
lesson applying to a sibling file, and this time it worked.

### The sharper question the file leaves open

> "An actual third adaptation would need a **different operator on the Lambert kernel**,
> not a renamed multiplication action or a translated sparse orbit."

So: with `K_n(x) = x^n/(1-x^n) = sum_k x^(kn)`, which operators `T` satisfy
`T[K_n] = K_(sigma(n))` for an index map `sigma`? Three exist, and only the first is in the
file:

| operator | action on the index | character |
|---|---|---|
| `M_a`: substitution `x -> x^a` | `sigma(n) = a n` | **FREE** -- iterates give a tower |
| `S_a`: coefficient section (keep degrees divisible by `a`, reindex) | `sigma(n) = n / gcd(n,a)` | **INVERSE of `M_a`** |
| `H_m`: Hadamard product with a fixed `K_m` | `sigma(n) = lcm(n, m)` | **IDEMPOTENT** |

All three verified as exact coefficient identities to degree 2400, and
`S_a . M_a = identity` on the kernel family, likewise verified.

**Neither new operator opens a mechanism.** `S_a` is the inverse of `M_a`, so it is the
base-`a` action the map already names -- the file's own verdict on renamed multiplication
applies verbatim. `H_m` is idempotent (`lcm(lcm(n,m),m) = lcm(n,m)`), so its iterates
collapse after one step and it generates no tower, hence no Mahler-type functional
equation.

### A false negative I nearly recorded

My first section check reported **False**, with counterexamples at `(n,a) = (1,5), (1,6),
(1,7)`. It was an artifact of my own comparison bound: `S_a` maps degree `d*a` to degree
`d`, so its output carries information only out to `M/a`, and I compared out to `M/4` --
past where any `a > 4` has source coefficients. Corrected to `M/a`, the identity holds with
no counterexamples. **READ EVERY ROW YOU LABEL**: I was one step from recording "the
section identity is false" as a finding.

### Verdict

**Negative, and it extends the breadth gate rather than closing the question.** The file
eliminated translation, sparse affine orbits, and `k`-adic substitution; this section adds
coefficient section and Hadamard-with-a-fixed-kernel. Five candidate operators, no third
adaptation.

**This is still a breadth gate, not a classification.** The open question is exactly which
index maps `sigma` are realisable by ANY operator on the Lambert kernel. The three found
are multiplication, its inverse, and a lattice join; whether a genuinely different `sigma`
-- say a multiplicative endomorphism like `n -> n^2` -- can be realised uniformly in `n` is
**not settled here**, and I have not proved it cannot.

### Nonclaim

No progress on Erdos 257. Section AP's named candidates were already eliminated in my own
directory, two further operators are eliminated here, and the general classification the
file asks for remains open.

## 60. The sibling lane's control rule, applied: section 46's census measured zero density

Task this iteration: consume the unread sibling corrections before generating anything new.
`erdos257_hole_geometry/` is READ-ONLY for me; what follows is consumption, not edit.

### 60.1 What the two unread documents actually owed me

**(a) `ResonanceOverlap.md` section 7, "Corrections this lane owes the spine".** Seven items.
Six are internal to that lane's own resonance and overlap lists -- the `17, 26` coincidence
(`p = 0.067`), the corrected D- and M-lists, `lam_M(k) = 2^(1-tau(k))`, the exact per-`k`
rates, the two-null reporting rule. None of them names an object my lane holds; this is
T25a again, shared vocabulary without shared objects.

**Item 6 is not like the others.** It is a general methodological rule:

> Band-matching by expected count is necessary but not sufficient. A control needs an
> OUTCOME screen as well as an EXPECTATION screen.

Every census in sections 45, 46 and 55 uses a marginal-preserving shuffle as its null.
That is an expectation screen and nothing else. I never asked why the control fires.

**(b) `ConsolidatedAccount.md` section 6.3** carries four corrections, all owed to that lane's
own spine -- the `k <= 43` window cap, the rank-budget dependence of `49` versus `50`, the
`q_min` normalisation `pi*sqrt(2)*2^(n/2)`, the non-unique `n = 4` witness. None touches me.
Its closing line is a general rule that does:

> A method adopted to avoid a timeout must not be carried into a regime where the exact
> computation is cheap.

That is **T37a stated as a law** -- independently reached, from a totient-skeleton
approximation carried to `k = 40` where the exact lcm is 1,487 bits and trivial. My excess
scripts carried `2^-delta` for eight sections where the exact atom is one line. Same class,
found twice in two programmes. It belongs on the standing list, not as an incident report.

**`ConsolidatedAccount.md` section 7** is that lane's global judgement: 257 more likely false
than true, but the corpus's confidence overstated. It is a CONFIRM for me, with content. By
its own section 3.4 a measure statement here is vacuous (`m(S_N) = 1` exactly, every `N`), and
by 3.2 an argument establishing genericity would prove the opposite of 257. So the register
in which that lane can compute is the register that cannot settle the question. My parity and
socket work lives in the arithmetic register -- the arrangement of `tau_A mod 2`, not its
measure -- which is precisely what their heuristic cannot see. The lanes are complementary,
and neither is redundant.

### 60.2 The outcome screen, run

The socket clause is `2^k | tau_A(N+k)`. **Zero is divisible by everything, so every zero
passes at every `k`, free.** A shuffle preserves the multiset, hence preserves the zero count
exactly. So for a support whose `tau_A` vanishes often, the control's socket run is a run of
ZEROS, and carries no information about the arithmetic of the nonzero values.

`scripts/zero_screened_control.py`, predictions and falsifier in the docstring before the run.
Falsifier: if a null carrying no arithmetic lands far from the recorded controls, zero density
is not the driver and this correction is withdrawn. `M = 10^6`, `nmax = 500,000`.

| cohort | `z` | observed | control A (full shuffle) | Bernoulli(`z`), NO arithmetic | control B (zeros pinned) |
|---|---|---|---|---|---|
| `N` (`d`) | 0.0000 | 5 | 6 | 0 | 7 |
| primes (`omega`) | 0.0000 | 2 | 2 | 0 | 3 |
| `{2^i}` (`v_2`) | 0.5000 | 3 | **17** | **16** | **5** |
| `{3^i}` (`v_3`) | 0.6667 | 5 | **31** | **32** | **6** |
| `3N` | 0.6667 | 8 | **33** | **31** | **10** |

**A Bernoulli process carrying no `tau` values at all reproduces control A to within 1, 1 and
2.** On the two cohorts with no zeros it gives 0 against 6 and 2, so there the control does
measure divisibility -- the screen discriminates rather than dissolving everything. Control B
destroys the odd-set arrangement exactly as control A does but pins the zeros at their true
positions; it collapses 17, 31, 33 to 5, 6, 10.

### 60.3 What that retracts

Section 46 read its controls two ways, and both are wrong.

- *"the control makes the obstruction visible by removing it"* (5 to 31). **No.** Control B
  removes the same obstruction and gives 6. The parity obstruction's removal is worth `5 -> 6`,
  which is nothing. The 31 was zero-run.
- *"Something else suppresses runs there"* for `3N`, 8 against 33. **There is no something
  else.** Against the screened control it is 8 against 10.

Both are spliced at their source above. With the repaired null the real supports sit at
`3/5`, `5/6`, `8/10` of chance -- a real direction, but **near chance**, and by this lane's own
method rule a near-chance measurement is never presented as a structural obstruction. So:

**The socket census's statistical channel is DEAD as a source of obstruction evidence.** It
carries nothing beyond the theorem it was decorating. That is an elimination: it closes a
channel I would otherwise have kept mining for a mechanism that was never there.

### 60.4 What does not change, and the prior art I rediscovered

Section 46's VERDICT is untouched. `maxrun <= maxgap(Odd_A) - 1` is proved, and its core is
machine-checked and constructive (`no_socketRun_of_odd_in_window`, axioms `[propext,
Quot.sound]`). The control was decoration around a theorem; only the decoration falls.

**T13/T29a pays off a third time in four iterations, and this time against me.**
`scripts/socket_depth_law.py` -- section 47, written one section after the framing now
retracted -- already says in its docstring that zero coefficients are EXEMPT, already derives
the `a = min A` sharpening `2^(K-a+1) <= max tau_A` from the fact that any `a` consecutive
integers contain a multiple of `a`, and already states:

> a shuffled sequence has no `min A` and can pack a long run out of scattered zeros. The
> control is therefore checked against parity alone, and that asymmetry is reported rather
> than hidden.

So s47 diagnosed this exact artefact and responded by DROPPING the control comparison. Section
46's prose was never reconciled with it, and the note has carried the contradiction between
lines 2764 and 2808 ever since. What is new here is only the quantification -- the Bernoulli
null reproducing control A to within 1, which converts "the control can pack zeros" into "the
control is zero-packing and nothing else" -- and the repaired control B that s47 declined to
build. The diagnosis was already mine. I did not read my own script.

### 60.5 An unexplained residual, stated as one

The *"worse than chance"* framing at line 2668 belongs to the section 45 BLOCK census, whose
clause is `tau_A(N+j) = tau_A(j) + 1`. **Zeros give no free pass there** -- a zero at `N+j`
would need `tau_A(j) = -1` -- so this correction does not transfer, and I have not edited it.
I tried the obvious analogue, predicting the block control from the marginal alone via
`p = sum_v P(tau = v) P(tau = v+1)`. For both `{2^i}` and `{3^i}` that gives `p = 1/6` and so
`log_6(5 x 10^5) = 7.3`, against recorded controls of **10 and 3**. One predictor, two cohorts,
neither matched. **The section 45 block control is not explained, and I am not going to dress
that up.** It is the next thing to screen, and until it is screened section 45's reading stands
as MEASURED-IN-RANGE with an unaudited null.

**Status.** No new mathematics about 257. One phantom mechanism eliminated, two claims
retracted at source, one control repaired, one general rule adopted from a sibling lane, and
one residual left open and labelled. Receipt:
`state/formal_math/erdos257_period_noncollapse/zero_screened_control_receipt.json`.

## 61. The block control was a lottery, and on four cohorts it could not have failed

Cross-index T39b, the residual section 60.5 left open. Section 45's *"worse than chance"*
reading had never been screened. It has now been, and it does not survive in the form it
was written -- but not for the reason section 60 would have predicted.

### 61.1 The clause is a covering condition, and my own docstring said so

`scripts/shifted_block_census.py` derives, before its run, that when `a | N` for every
`a in A` with `a <= K`,

    tau_A(N + j) - tau_A(j) = #{a in A : a > K and a | N + j},

so the shift clause says **each of `N+1, ..., N+K` has exactly one divisor in `A` above
`K`** -- a covering-type condition, which at `A` = primes is Pratt's construction. That is
the outcome screen, already written, in algebra. The same docstring states the exact
per-cohort caps as PREDICTIONS. **I did not need to derive any of this. I needed to read
my own file.** T13/T29a, fifth payoff in six iterations.

### 61.2 Four of six cohorts: the real `K` is a theorem, so the control had zero power

Corpus convention (`build_tau`): `A` contains 1.

| `A` | `tau_A` | argument | cap |
|---|---|---|---|
| `N` | `d` | `K>=1` forces `N+1` prime; `K>=2` forces `N+2=p^2`; `K>=3` forces `N+3=q^2` with `q^2-p^2=1`, impossible. `K=2` needs `N+1` prime AND `N+2=p^2`, but `N+1=(p-1)(p+1)` is composite for `p>=3` | **`K=2` at `N=2` only** |
| `{2^i}` | `v_2+1` | `K>=1` forces `N+1 = 2 mod 4`, so `N` is odd and `N+2` is ODD; `K>=2` needs `v_2(N+2)=2` | **`K<=1`** |
| `{3^i}` | `v_3+1` | `K>=1` forces `3 || N+1`; `K>=2` forces `3 || N+2`; both cannot hold | **`K<=1`** |
| `3N` | `d(m/3)` or 0 | `K>=1` forces `3 | N+1` and `d((N+1)/3)=1`, so `(N+1)/3 = 1` | **`N=2` exactly** |

All four agree with the landed census receipt (`max_K` 2/1/1/1 at `argmax_N` 2/1/2/2).
**A control comparison against a proven constant cannot come out any other way.** The
sibling lane names this exactly: `DyadicAutonomousOrbits.md` section 3d, *"any check
confined to ranks <= 16 has power exactly zero -- it is not that no overhang was found, it
is that none exists to find."*

### 61.3 Where the control does vary, it is a lottery

`control_census` shuffles the WHOLE array `1..M`. So the values at the small indices
`j = 1..K` are shuffled too, and every `N` is tested against **one fixed word**
`w = (tau'(1), ..., tau'(K))` drawn once per seed; `K >= 1` is conditioned on the single
realised value `tau'(1)`. `scripts/block_control_stability.py`, 8 seeds, `M = 10^6`,
`nmax = 5 x 10^5`:

| cohort | real | recorded control | control range over 8 seeds |
|---|---|---|---|
| `3N` | 1 | 1 | `1..1` |
| `N` | 2 | 1 | `0..1` |
| `{2^i}` | 1 | **3** | **`5..8`** |
| `{3^i}` | 1 | **10** | **`2..10`** |
| squares | 5 | **5** | **`4..10`** |
| primes | **12** | 8 | `5..9` |

The recorded `{2^i}` draw sits **below its entire range**; the `{3^i}` draw is the **top**
of its. The screen still discriminates -- `N` and `3N` are stable at `0..1` and `1..1` --
so this is not a screen that flattens everything.

### 61.4 What that retracts, and what survives

- The squares row **flips**. Section 45 read `5` against `5` as "no structure at all". With
  the control spanning `4..10`, that reading rests on having drawn a 5. Spliced at source.
- *"Worse than chance"* is **vacuous, not false**, on the four theorem rows. Spliced.
- **`primes` survives.** Real `12` exceeds `9`, the maximum over all 8 control draws. This
  is the Pratt row the docstring names as the calibration, and it is the one row of the six
  carrying evidential content.

**Section 45's evidential base goes from six rows to one, and that one holds.** The
section's VERDICT -- the shifted-block mechanism eliminated for 257 -- is untouched; it
rests on the algebra of section 44 and the caps above, not on the control.

### 61.5 A wrong prediction, recorded

I predicted the control from the marginal alone via `p = sum_v P(tau=v) P(tau=v+1)`. That
gives `p = 1/6` for BOTH `{2^i}` and `{3^i}`, hence one predicted `K ~ log_6(5x10^5) = 7.3`
for both, and it orders them `{2^i} > {3^i}` since `P(tau'=2)` is `1/4` against `2/9`. The
truth is `5..8` against `2..10`, the other way round. **The predictor averages over the head
word, which is precisely the quantity that must not be averaged.** Eighteenth wrong
prediction on record.

### 61.6 Two rules adopted, and one of my own corrected

From `DyadicAutonomousOrbits.md`: section 3d gives **zero power** (T40) -- compute what a
check could possibly have returned before reading its negative. Section 4(a) gives
**compression defect** (T40a): *"the spine dropped it in compression... that is a
compression defect, not a lane error, and it is the more dangerous kind, because the spine
is what gets read."* That is section 60's failure named as a class. Its section 4(b) reports
a receipt refuting one claim produced while establishing another **for the fourth time** --
the same count this lane has reached. Two independent programmes, identical failure,
identical rate. That makes it structural to how this corpus is built.

And a correction to a rule I wrote myself last iteration. I recorded T40d as "a stale
self-lease may not clear within a turn; commit the disjoint subset and defer". **The defer
was unnecessary.** `work_ledger.py session-release-claim --session-id <mine> --path <p>`
releases it, and the path took two calls because that session held two claim rows on it.
The correct rule is: **a lease you own is yours to release; check the CLI before routing
around your own claim.**

**Status.** No new mathematics about 257. One evidence base audited down from six rows to
one, two readings retracted at source, four caps promoted from measurement to theorem, two
methodological laws adopted, one wrong prediction and one wrong operational rule recorded.
Receipt: `state/formal_math/erdos257_period_noncollapse/block_control_stability_receipt.json`.

## 62. The ledger was stale, and T40 answered the question without running anything

Residual (r): section 55's ledger controls had never been screened, and they belong to the
marginal-preserving shuffle family that failed in section 60 (zero density) and section 61
(lottery, zero power). The plan was to re-run them over eight seeds. **That was not
necessary, and T40 is why.**

### 62.1 Section 55 has exactly one control, and it is moot

The ledger's six rows carry one control between them: the block row, where
*"a marginal-preserving shuffle of `tau_{A*}` attains a block of length 2 at `N = 1031`,
against the real sequence's 3 at `N = 6`."* Apply T40 before computing -- could that
comparison have come out any other way? **No, because section 56 proves the real value.**
Section 56's own closing line already says it: *"the control is irrelevant to a theorem."*

So the answer to (r) required no seeds, no instrument and no receipt. **Reading beat
running.** That is the entire point of T40, and it is the sixth time in seven iterations
that the answer was already on disk (T13/T29a).

### 62.2 And section 55's control reading was correct

Credit where it is due, because the last two sections have not been kind to my controls.
Section 55 wrote: *"That is barely above the coincidence null, and I will not present it as
a structural obstruction."* **That is the correct call, made at the time, on the evidence
then available.** It is the one control in this corpus that was read right. The method rule
works when it is actually applied; sections 60 and 61 are what happens when it is not.

### 62.3 The real defect is that the ledger went stale

Section 55 calls its table *"the evidence ledger, which is the actual deliverable"* and
signs off *"That is the honest shape."* It was two sections out of date on **both** of its
MEASURED-IN-RANGE rows:

| row | as section 55 recorded it | what was already true |
|---|---|---|
| block / transplant | `MEASURED-IN-RANGE`, and weak -- control 2 | **PROVEN** in section 56, `K = 3` only at `N = 6` |
| `hclose` | min excess `0.374` | `0.374` **RETRACTED** in section 57; exact min `0.206435` at `N = 1` |

and its count line read *"Three PROVEN, one BOX-ONLY, two MEASURED-IN-RANGE"* when the
truth was four, one, one. **Section 56's own ledger is stale too** -- it corrected the block
row (it was the section that proved it) and left `0.374` standing in the `hclose` row.
All four places are now fixed at source, plus the `0.374` in section 55's prose.

**This is T40a, the compression defect, in its purest form.** The corrections existed, in
this same file, in the two sections immediately following. What failed is propagation into
the summary -- and the summary is the thing a reader reaches for. The sibling lane's
formulation is exact: *"that is a compression defect, not a lane error, and it is the more
dangerous kind, because the spine is what gets read."*

### 62.4 The operational rule, fourth version and this time from evidence

I have now written the lease rule wrong three times: "defer, do not release" (wrong), "a
lease you own is yours to release" (over-general), "a prior session releases, the live one
does not" (wrong -- `blockscreen` was prior and appeared not to release). The truth is
duller. **`session-release-claim` releases ONE claim row per call, and a session holds one
row per preflight it ran.** `blockscreen` had accumulated many. Every release I issued
succeeded -- `status: released`, `rc = 0` -- and I never looked, because I was reading the
next preflight's verdict instead of the release's own receipt. **Drain until `released` is
empty, and read the receipt of the command you actually ran.** T37b's cousin: I inferred
failure from an unchanged downstream signal without reading the upstream return.

**Status.** No new mathematics about 257. One residual closed by reading rather than
running, four stale ledger cells and one stale prose figure corrected at source, one honest
past judgement confirmed, and one operational rule finally grounded in its own receipt.

## 63. The T41 sweep: the ledger had THREE copies, and one exact value covers two supports

Section 62 wrote T41 -- *"grep the RETRACTED VALUE across the whole file"* -- and did not do
it. This is that sweep, run over three files and every retracted claim on the residual list.

### 63.1 What was swept, and what was found

| file | `0.374` | `0.367` | "worse than chance" | genuinely stale |
|---|---|---|---|---|
| `CertificateSocketCollapse.md` | 11 | 3 | 3 | **2 lines** |
| `ERDOS257_CROSS_INDEX.md` | 4 | 3 | 2 | **5 lines** |
| `docs/.../erdos257_computational_exhaustion_map_2026_08_22.md` | 0 | 0 | 0 | **0 -- CLEAN** |

**Raw hit counts are not stale cells.** Most occurrences are the retraction text itself,
which must quote the old number to retract it: section 57's comparison table needs its
`0.374479` column to show the discrepancy, and T36a, section 58's correction table and
section 62's account all name `0.374` deliberately. Those are LEFT, and left on purpose.
Reading every line before labelling it is the whole job here.

**Seven lines across six sites were genuinely stale, and all are fixed at source.**

### 63.2 The find that matters: the ledger had three copies, not two

Section 62 corrected the `A*` evidence ledger in section 55 and section 56 and reported the
job done. **There was a third copy, in the cross-index at T34a**, and it was stale on BOTH
rows -- `hclose` still reading `0.374`, and the block row still reading
*"MEASURED-IN-RANGE, and WEAK"* six sections after section 56 proved it. Section 62's own
closing claim that "all four places are now fixed" was therefore wrong; there were five.

**Corollary for T41: count the copies before declaring a projection fixed.** Grepping the
value found this in seconds; not grepping it is what let section 62 ship an incomplete fix
while writing the rule that would have caught it.

The cross-index also carried, at the section 45 entry, *"these supports are worse than
chance. Squares score real = control = 5"* -- both halves refuted (the first vacuous by
T40c, the second a single lottery draw against a `4..10` range by T40b). Fixed.

### 63.3 A new residual, and I am not going to paper over it

T36a states: *"Section 52's `min excess 0.367` and section 55's `min excess 0.374` are
approximation values and are TOO HIGH. The exact minimum over the same range is
**`0.206435` at `N = 1`**."* But **section 52 and section 55 are about DIFFERENT SUPPORTS** --
section 52's `A` versus `A* = N \ E` -- and T36a assigns one exact value to both. I have not
verified that. It may be right (both minima sit at `N = 1`, where the universal identity
`excess(1) = y` bites), it may be a transcription of the `A*` computation onto a row it was
never run for.

I have splice-marked both sites faithfully to what T36a says and **flagged the cross-support
claim as residual (u)**, unverified. It is decoration either way -- both verdicts turn only on
the minimum being bounded away from zero -- but **a wrong trap is worse than a wrong number,
because traps steer the next iteration.** That is what makes it worth checking rather than
quietly adopting.

### 63.4 The lease, finally pinned

`session-release-claim` acts on **ONE PATH PER CALL**. Passing two `--path` flags releases
the first and silently leaves the second, which is why my drain loops kept reporting
`released: 0` while the preflight still collided. The receipt says exactly which:
`status: released` with the claim row, versus `status: noop`,
`reason: no_matching_active_claim`. **Release one path per call and read `status`.** Fifth
version of this rule, and the first one derived from the receipt of the failing call rather
than from a downstream symptom.

**Status.** No new mathematics about 257. Three files swept, 26 raw hits read, seven stale
lines fixed at source across six sites, one previously-unknown third ledger copy found and
corrected, one exhaustion map confirmed clean, one unverified cross-support claim promoted to
a named residual.

## 64. T36a was wrong: one exact value, two different supports, and the identity that decides it

Residual (u), raised in section 63 and left open there rather than papered over. **T36a is
wrong, and the mathematics that shows it was already in this lane's own carried identity.**

### 64.1 The identity does the work; the computation only confirms it

The universal identity this lane already holds: for any `A` with `1 not in A`,
`Phi_A(1) = 2y`, hence **`excess_A(1) = y_A`**. Directly: the exact atom is
`(2^(N mod a) - 1)/(2^a - 1)`, and at `N = 1` every `a >= 2` has `1 mod a = 1`, so the atom
collapses to `1/(2^a - 1)` and

    excess_A(1) = sum_{a in A, a >= 2} 1/(2^a - 1).

**The `hclose` excess at `N = 1` IS the Erdos 257 sum for `A`.** So T36a's claim -- one exact
minimum covering sections 52 and 55 -- is the claim that two different supports have the same
257 sum. Stated that way it is obviously wrong, and it did not need a computation to doubt.
T13/T29a, seventh payoff: the identity was already on the carried list.

### 64.2 The numbers

Exact atom, the T37a-safe form, with Erdos-Borwein calibrating in the same run at `1.606695`:

| support | `excess(1)` | is this T36a's `0.206435`? |
|---|---|---|
| section 52, `A = N \ {2^i}` | **`0.202758`** | **no** |
| section 55, `A* = N \ E`, `E = ({2^i : i>=1} u {4p}) \ {8}` | **`0.206435`** | **yes** |

Gap `0.003677`. Both `{2^i}` conventions (`i >= 0` and `i >= 1`) give section 52 the same
`0.202758`, because the `a = 1` atom vanishes at `N = 1` anyway -- so the convention
ambiguity that would have forced a guess turns out not to bite. Over section 52's own stated
range -- every `2^i - 1` to `2^11` and every `lcm(1..k)` to `k = 11`, 19 values -- the
minimum is `0.202758`, **attained at `N = 1`**.

**So T36a's ARGMIN was right and its VALUE was wrong.** `0.206435` is the `A*` number,
transcribed onto section 52's row where it was never computed. Fixed at source in T36a
itself and in both splices that section 63 had written citing it.

### 64.3 What this does and does not change

**Nothing about either verdict.** Both rows turn only on the minimum being bounded away from
zero, and `0.202758` and `0.206435` are both comfortably positive. Section 52's candidate
still dies on base-adaptation; `A*`'s `hclose` row still reads FAILS.

What it changes is the trap. **A wrong trap is worse than a wrong number, because a number
sits still and a trap steers the next iteration.** Section 63 flagged this rather than
adopting it, and that was the right call: had I quietly propagated `0.206435` onto section
52's row, the corpus would now carry a fabricated measurement for a support nobody had run.

**Status.** No new mathematics about 257. One trap refuted and corrected at source, one
value replaced by the correct one for its own object, one identity re-derived that was
already on the list, and one residual closed with a definite answer rather than a hedge.

## 65. Sections 19-44 screened: a clean bill, and T40 turns out to be native

Residual (s), the last named open item. Sections 19-44 -- 1,644 lines -- had never been
screened for the control defects that sections 60-63 found downstream.

### 65.1 The screen, and its result

Patterns swept across the whole range: `control`, `shuffl`, `chance`, `MEASURED-IN-RANGE`,
`coincidence`, `null`. **Ten hits total.** Zero for `shuffl`, zero for `chance`, zero for
`MEASURED-IN-RANGE`.

Read individually (T42b), the ten split as:

| what it is | count | example |
|---|---|---|
| mathematical "control" -- bounding a quantity, not a statistical null | **7** | *"Erdos need only control `O(k^2)` primes by CRT"*; *"uncontrolled extra prime factors"*; *"given control of `c(M + j)`"* |
| `null` in the MEASURE sense | 1 | *"those criteria see a null set and report failure"* |
| a real control, **already self-corrected at the time** | 1 | the `M = 1` row (below) |
| a real control, **correctly power-screened at the time** | 1 | the broken-hypothesis check (below) |

**Sections 19-44 carry no statistical control of the marginal-preserving shuffle family at
all.** The defect class that sections 60 and 61 found does not exist here, because the
instrument that produced it had not been built yet. **Nothing to re-label. Clean bill.**

### 65.2 The one control that was wrong was caught when it was written

> *"My first run printed a control row at `M = 1` labelled 'bounded, `hclose` would FAIL on
> this sequence'. Reading the numbers, `delta_min` there was `4, 8, 16, 32, 64, 128` --
> **growing**, not bounded. The label was false and the control was in fact a second
> witness. Never label a row without reading it."*

Caught, corrected, and generalised into the standing rule READ EVERY ROW YOU LABEL, in the
same paragraph. No action.

### 65.3 T40 is not a foreign import. I had it, used it, and stopped

The other real control, from the formalisation-calibration section:

> *"Calibrated. On synthetic `c` with the shift imposed only on `1..K` ... the two sides
> differ by `75 / 1.32e123 ~ 5.7e-122`, which is precisely the depth-400 truncation tail.
> **Control with the hypothesis broken at `k = 3` by `+5`: difference exactly
> `0.625 = 5 * 2^-3`, the predicted magnitude -- so the check has power and is not
> vacuously passing.**"*

That is **exactly T40**: a deliberately broken hypothesis, run to confirm the check could
have failed, with the failure magnitude predicted in advance. It is a better instance than
the sibling lane's, because it does not merely reason about power -- it MEASURES it.

**So T40 was native to this lane, applied correctly here, and then not used again for
roughly twenty sections** -- across the socket census, the block census and the section 55
ledger, all of which needed it. In section 61 I imported it from
`DyadicAutonomousOrbits.md` section 3d as though it were new. It was not new; it was
forgotten. **Eighth T13/T29a instance, and the most expensive: the cost was not a wrong
number but four rows of zero-power evidence and one 8-seed run that never needed to happen.**

### 65.4 The identity is forty sections old

Line 695 of the range already carries, in full:

> *"The primes row of section 9's table reports min excess `0.516943`, which is equal to `y`
> itself. That is not a coincidence and not an error: for any `A` with `1 not in A`, every
> `a >= 2` has `1 mod a = 1`, so `Phi_A(1) = sum_a 2/(2^a - 1) = 2y`, hence
> `excess(1) = y`, for EVERY such A."*

This is the identity that refuted T36a in section 64, stated here with its derivation and
with the correct warning that the printed figure is a universal constant and not a fact
about the primes. **Section 64 did not discover it. Section 64 remembered it.**

### 65.5 The section-number collision, settled

Three sibling commits name section numbers I also own -- `2fa68afd77` (*"it refutes my own
section 40"*), `f22543e04a` (*"sections 42-43 landed"*), `b23b61a164` (*"two attempts at the
section 44 target"*). **Every file in all three is under `erdos257_hole_geometry/`.** Those
are their section numbers, not mine. **The two programmes number sections independently, so
a bare "section N" in a commit message is ambiguous across lanes** -- resolve it by the
touched paths, never by the number. T25a again.

**Status.** No new mathematics about 257. Residual (s) CLOSED as a clean bill: ten hits read,
zero re-labelled, zero shuffle-family controls present. Two prior controls confirmed sound,
one of them a correct power screen predating T40 by twenty sections. The `excess(1) = y`
identity located at its true origin. Three foreign section-number collisions resolved as
false alarms. **All named residuals (a)-(u) are now closed or standing as recorded facts.**

## 66. The socket criterion: `Odd_{N\E} = Sq XOR Odd_E`, and containment was never the mechanism

The audit cycle is closed, so this returns to the mathematics. The target was to turn the
construction rules T31a/T32a/T33a-c into a theorem eliminating a whole FAMILY rather than one
witness. **The theorem I set out to prove is false. The one that replaced it is stronger.**

### 66.1 The candidate died on the T25 check, in one line

Candidate: *if `A = N \ E` with `E` contained in a fixed progression `dN`, `d >= 2`, then
`Odd_A` is syndetic and the socket mechanism kills `A`.*

Check it against `A = N` first, as T25 demands. `E = {}` is contained in **every** `dN`.
`Odd_N = {m : d(m) odd} = Sq`, the perfect squares, with gaps `~2 sqrt(m) -> infinity`. **Not
syndetic. The candidate is false.** Measured maxgap at `M = 60000`: `487`, against `2 sqrt(m)
= 490`.

That refutation is trivial, so here is a substantive one. **`E = 4N` is INFINITE, is contained
in `4N`, and `A = N \ 4N` does not die.** In closed form: `tau_{4N}(m) = d(m/4)` when `4 | m`
and `0` otherwise, so `tau_{4N}(m)` is odd exactly when `m/4` is a square, i.e. at
`m = 4k^2 = (2k)^2` -- which are themselves squares. Hence

    Odd_{N \ 4N} = Sq XOR {even squares} = {ODD SQUARES},

with gaps `(2j+3)^2 - (2j+1)^2 = 8j + 8 -> infinity`. Predicted maxgap near `M = 60000`: about
`980`. **Measured: `968`.**

### 66.2 What is true instead, and it is a reduction of the whole family

For `A = N \ E`, a divisor of `m` lies in `A` exactly when it is not in `E`, so
`tau_A = d - tau_E` pointwise. The parity map is `F_2`-LINEAR -- that is T30, already on this
lane's books -- and `d(m)` is odd exactly at squares. Therefore

> **Theorem (socket criterion).** For every `E` and `A = N \ E`,
> **`Odd_A = Sq XOR Odd_E`.**
> Consequently the socket mechanism kills `A` **if and only if `Odd_E` is syndetic.**

Both directions of the corollary are two lines. If `Odd_E` is syndetic with gap `g`: between
consecutive squares `k^2` and `(k+1)^2` there is a stretch of length `2k` containing none, so
on that stretch `Sq XOR Odd_E = Odd_E`, and toggling at most one point per square gives
`Sq XOR Odd_E` gap `<= 2g`. Conversely if `Odd_E` has gaps `L_k -> infinity` at positions
`m_k -> infinity`, then inside such a gap `Sq XOR Odd_E` is exactly `Sq`, whose local gaps are
`~2 sqrt(m_k) -> infinity`; so `Sq XOR Odd_E` has gaps `>= min(L_k, 2 sqrt(m_k)) -> infinity`.

**This reduces the socket question for the entire complement family to a property of `E`
alone.** It is a one-way result: it does not decide any `A`, it decides which question to ask.

### 66.3 The check, with calibration in the same run

`scripts/socket_parity_criterion.py`, predictions and falsifier in the docstring before the
run. Identity verified at EVERY `m <= 60000`, `M = 200000`.

| `E` | identity holds | maxgap `Odd_E` | maxgap `Odd_A` | socket |
|---|---|---|---|---|
| `{}` (`A = N`) | **yes** | 0 | **487** | survives |
| `{2^i : i>=1}` | **yes** | 4 | 4 | DEAD |
| primes | **yes** | **20** | 14 | DEAD |
| `{2^i} XOR primes` | **yes** | 15 | 15 | DEAD |
| `4N` | **yes** | **972** | **968** | survives |

The primes row reproduces `maxgap(Odd_primes) = 20`, a number landed long before this section
-- calibration on a known value in the same run.

### 66.4 Containment was never the mechanism

T33b's `4N` clause says: *if `D` is contained in `4N`, no element of `D` divides any
`m == 2 mod 4`, so the syndeticity SURVIVES.* That is a statement about a PERTURBATION `D`
leaving an already-syndetic set intact. **It is not, and never was, a claim that a support
whose deleted set lives in a sublattice dies.** I read it as the latter and the reading is
refuted both ways:

- `E = 4N` is inside `4N` and **survives**;
- `E = primes` is inside no proper progression (they meet every coprime class) and **dies**.

**Sublattice containment neither implies nor is implied by socket death.** The real invariant
is the parity of `tau_E`, and nothing else.

### 66.5 The escape condition, stated

A complement support `A = N \ E` survives the socket mechanism **iff `Odd_E` has unbounded
gaps** -- iff there are arbitrarily long runs of `m` on which `E` has an EVEN number of
divisors, zero included. That is the constraint any open-class survivor of this shape must
satisfy, and it is now exact rather than heuristic.

**And the honest limit on it.** `N \ 4N` satisfies the escape condition and is nonetheless
**eventually PERIODIC** -- it is `{m : m !== 0 mod 4}` -- so it is already settled by solved
class (i), the Lambert/AP route. **Surviving one mechanism is not surviving the problem, and
this falsifier is not a candidate.** The escape condition is necessary, not sufficient, and
anyone reading section 66 as producing a survivor has it wrong.

### 66.6 Parameter box

`M = 200000`, identity checked at every `m <= 60000`, five cohorts. The `maxgap` figures are
window-dependent and monotone in the window: `maxgap(Odd_primes) = 20` is PINNED to this box,
and the script now reports it `n/a_off_default_box` rather than FALSE when run smaller -- a
pinned calibration asserted outside its box is a category error, not drift.

**Status.** One candidate theorem refuted, twice. One general theorem proved and machine
checked at every point of its range: the socket question for all complement supports reduces
to syndeticity of `Odd_E`. One framing corrected -- containment was never the mechanism. One
escape condition stated exactly, with its insufficiency stated in the same breath. Receipt:
`state/formal_math/erdos257_period_noncollapse/socket_parity_criterion_receipt.json`.

## 67. Sparsity is the WORST parity, not the safest -- and the escape door leads back to periodicity

Section 66 reduced the socket question for complement supports to one property of `E`:
`Odd_A = Sq XOR Odd_E`, so the socket kills `A = N \ E` iff `Odd_E` is syndetic. This asks
whether the escape door -- `Odd_E` with unbounded gaps -- opens onto the OPEN class
(aperiodic AND not base-adapted).

**I went in with a dichotomy and it was backwards.**

### 67.1 One line of algebra, before any computation

    Odd_E = {m : tau_E(m) odd}  CONTAINS  {m : tau_E(m) = 1}.

Let `e1 = min E`. If `m` is a multiple of `e1` divisible by no OTHER element of `E`, then
`tau_E(m) = 1` exactly -- **odd** -- so `m` lies in `Odd_E`. **Sparsity does not make `tau_E`
even; it makes `tau_E` equal to ONE, which is the worst possible parity.** The sparser `E`
is, the larger the fraction of `e1 N` on which `tau_E = 1`, and `e1 N` is syndetic with gap
`e1`.

The contrast is `E = 4N`, which is not sparse at all: every multiple of 4 is in `E`, so
`tau_{4N}(m) = d(m/4)`, typically LARGE and EVEN, odd only at `m = 4k^2` (section 66).
**Density in a progression, not sparsity, is what makes `tau_E` even.**

I had it the other way round -- expecting thin `E` to give thin `Odd_E`. Nineteenth wrong
prediction on record, and it cost nothing only because the algebra was cheap enough to run
first.

### 67.2 The measurement, and the column that shows the mechanism

`scripts/sparse_kills_socket.py`, nine families, `M = 120000`, gaps to `m <= 60000`.

| `E` | kind | `min E` | maxgap `Odd_E` | density `Odd_E` | **density `tau_E = 1`** | socket |
|---|---|---|---|---|---|---|
| `{2^i}` | sparse | 2 | **4** | 0.333 | **0.250** | KILLS |
| `{2^(2^i)}` | sparse | 2 | **4** | 0.309 | **0.250** | KILLS |
| `{k!}` | sparse | 2 | **4** | 0.368 | **0.333** | KILLS |
| `{k^2}` | sparse | 4 | **8** | 0.342 | **0.275** | KILLS |
| primes | sparse | 2 | 20 | 0.504 | **0.103** | KILLS |
| `4N` | dense in progression | 4 | **972** | 0.002 | **0.000** | survives |
| `6N` | dense in progression | 6 | **1194** | 0.002 | **0.000** | survives |
| `4N XOR {2^(2^i)}` | perturbed | 8 | **12** | 0.191 | 0.029 | KILLS |
| `6N XOR {k!}` | perturbed | 2 | **4** | 0.368 | 0.333 | KILLS |

**The `tau_E = 1` column is the mechanism, measured: exactly `0.000` for both survivors and
between `0.10` and `0.33` for every killer.** Nothing else in the table separates the two
groups so cleanly -- the raw `Odd_E` density does (0.002 vs 0.3), but only because it is
downstream of the same cause.

### 67.3 Perturbation restores death, and `F_2`-linearity forces it

Both survivors are eventually PERIODIC, so by T45b they are already settled by solved class
(i) and are not open-class candidates. The obvious repair is to perturb one into
aperiodicity. **It does not work, and section 66's linearity says why before the run:**
`Odd_{P XOR S} = Odd_P XOR Odd_S`, and a syndetic `Odd_S` dominates a sparse `Odd_P`. Since
section 67.1 shows every sparse `S` has `Odd_S` syndetic, **every sparse perturbation of a
survivor restores socket death.** Measured: `4N` goes from gap 972 to **12**, `6N` from 1194
to **4**.

### 67.4 What this is, stated at its true strength

**The gap is not inhabited by anything I could construct: `gap_inhabited = False` across all
nine families.** Every `E` with non-syndetic `Odd_E` came with periodicity, and every
perturbation that restored aperiodicity restored syndeticity with it.

**This is a NARROWING, not a proof of emptiness**, and the distinction matters. What is
PROVEN is the containment `Odd_E ⊇ {m : tau_E(m) = 1}` and section 66's criterion. What is
MEASURED-IN-RANGE is that nine families fall on the two sides described. **No theorem here
says the gap is empty.** What the evidence does support is a sharp structural demand:

> Socket survival for a complement support requires almost every multiple of `min E` to
> carry a SECOND divisor in `E`.

That is a covering demand on `E`, and covering `min(E) * N` densely is exactly what drives
`N \ E` toward periodicity -- the other solved class. **The escape door from the socket
mechanism appears to open onto solved class (i), not onto the open class.** Proving that
implication, rather than measuring it on nine families, is the next real target.

### 67.5 Parameter box, and a contended-surface note

`M = 120000`, gaps to `m <= 60000`. The sparse families are INFINITE as families but only
their truncations below `M` are exercised; a finite truncation of an aperiodic family is
eventually periodic, so aperiodicity is a property of the family, not of what this run sees.

**Separately: `docs/formal_math/erdos257_computational_exhaustion_map_2026_08_22.md` is
being edited by another lane** (`99f53f89ed`, +96/-2), which also added its own files under
`ErdosProblems/Erdos257/`. **Section 63's finding that the map was clean of retracted values
may now be stale, and the map is contended** -- do not claim it without re-checking. Two
further sibling commits (`db3c59fd30` "corrects my sections 44, 44a and 45", and the batch-9
chain) touch only `erdos257_hole_geometry/`: their section numbers, not mine (T44a).

**Status.** One intuition refuted by one line of its own algebra. One mechanism isolated and
measured -- the `tau_E = 1` density, `0.000` for survivors against `0.10`-`0.33` for killers.
One repair route closed by `F_2`-linearity before it was tried. One honest narrowing, stated
as MEASURED-IN-RANGE over nine families and explicitly NOT a proof of emptiness. Receipt:
`state/formal_math/erdos257_period_noncollapse/sparse_kills_socket_receipt.json`.

## 68. Both exits are solved classes -- and the nullity box has a PROVEN blind spot

Section 67 left a conjecture (non-syndetic `Odd_E` forces periodicity) and a named candidate
family neither branch covered: positive-density aperiodic `E`, canonically Thue-Morse. This
iteration answers the candidate, fails a prediction, and gets something better than either.

### 68.1 The candidate was answered on my own disk, nine sections ago

**T31b, already landed:** *"Adapted: `N` `14,9,8`; `{2^i}` `12,0,10`; `{3^i}` `0,12,0`;
**Thue-Morse `5,0,0`**."* Thue-Morse fires at `k = 2` with nullity 5. **It is BASE-ADAPTED --
solved class (ii), Nishioka.** The canonical family section 67 nominated as the one neither
branch covers is covered, and was covered before section 67 was written. No computation was
needed to answer it. **T13/T29a, ninth payoff in ten iterations.**

### 68.2 A prediction that failed, and the algebra that explains the failure

I predicted `4N` and `6N` would both read ADAPTED, since `Y_{dN}(x) = x^d/(1-x^d)` is
RATIONAL and the corpus already notes (cross-index line 278) that `Y_N = x/(1-x)` being
rational forces nullity `> 0`. Measured:

    4N -> [4, 2, 2]   ADAPTED, as predicted
    6N -> [0, 0, 0]   NOT adapted in the box -- prediction WRONG

Twentieth wrong prediction on record. **But the algebra survives and explains the miss
exactly.** A rational `Y = P/Q` yields the order-0 Mahler relation `Q(x) Y(x) = P(x)`, and
here `Q(x) = 1 - x^d` has **degree `d`**. The detector's box is `(d = 2, D = 5)` -- degree at
most 5. So the relation is admissible **iff `d <= 5`**. Tested across `d = 1..10`:

| `d` | `deg Q = d` | nullity `(k=2,3,4)` | predicted |
|---|---|---|---|
| 1 | 1 | `14, 9, 8` | FIRE |
| 2 | 2 | `10, 6, 4` | FIRE |
| 3 | 3 | `6, 3, 3` | FIRE |
| 4 | 4 | `4, 2, 2` | FIRE |
| 5 | 5 | `2, 1, 1` | FIRE |
| 6 | 6 | `0, 0, 0` | **MISS** |
| 7-10 | 7-10 | `0, 0, 0` | **MISS** |

**The split is exact at `d = 5/6`, ten for ten**, and the nullity decays `14, 10, 6, 4, 2, 0`
precisely as the spare degree budget `D - d` shrinks to zero. `3N` reproduces T31b's landed
`6, 3, 3` exactly; `N` gives `14, 9, 8` and `{2^(2^k)}` gives `0, 0, 0` -- three calibrators
hit in the same run.

### 68.3 `6N` is a PROVEN false negative of the nullity instrument

`6N` has a rational generating function, so a Mahler relation EXISTS; the detector reads
`0, 0, 0` because that relation needs degree 6 and the box stops at 5. **This is the first
concrete witness that a `0,0,0` reading can sit on a provably ADAPTED set.**

T31c already said this abstractly -- *"Nullity `0` at `(d=2, D=5)` rules out relations in
that box only. It is not a proof that no Mahler relation exists at any order or degree."* --
and every `0,0,0` in this corpus was correctly labelled BOX-ONLY on that basis. **No verdict
changes.** What changes is that the caveat now has a witness instead of a warning:
**primes `0,0,0`, `{2^(2^k)}` `0,0,0`, `A*`'s non-adaptation row (T31c), and the greedy
supports of `1/21`, `4/9`, `3/(2^7-1)` all fail to exclude a relation of degree `>= 6`.**
That is what BOX-ONLY has always meant; it is now demonstrably not a formality.

### 68.4 What this proves about the escape door, upgrading section 67

Section 67 measured that the socket escape leads back toward periodicity. For one important
case that is now PROVEN, and it is stronger than periodicity alone:

> **If `E` is a finite union of arithmetic progressions, then `Y_E` is RATIONAL, so `E` is
> base-adapted -- solved class (ii) -- AND `N \ E` is eventually periodic -- solved class
> (i). Both at once.**

Rationality is immediate: a finite union of APs has generating function a finite sum of
`x^{a_i}/(1 - x^{d_i})`, and the order-0 relation follows. **So section 67's two survivors,
`4N` and `6N`, are each in TWO solved classes, and the second one is proved rather than
measured** -- `6N` by rationality despite the detector's silence.

**The escape door from the socket does not open onto one solved class. It opens onto both.**

### 68.5 What is still NOT proved

Section 67's demand was `E` **dense in a progression**, which is weaker than **a finite union
of progressions**. This section proves the union case and says nothing about the general
dense case. **An `E` that is dense in `dN` without being a finite union of APs remains
unexcluded**, and Thue-Morse does not fill that role because it is adapted for an unrelated
reason. **The gap is narrower and still not shown empty (T46b stands.)** Also unproved: that
non-syndetic `Odd_E` forces density in a progression at all -- section 67 gave that as a
structural demand read off the `tau_E = 1` mechanism, not as a theorem.

**Status.** One candidate family closed from disk without computation. One wrong prediction
recorded and its failure explained exactly. One instrument blind spot characterised and
proved, with a concrete witness where only an abstract caveat existed. One upgrade of section
67 from MEASURED to PROVEN on the union-of-progressions case, and an explicit statement of
what that upgrade does not cover. Receipt:
`state/formal_math/erdos257_period_noncollapse/both_exits_receipt.json`.

## 69. The box-widening probe: `A*` survives, and the calibrator fires on nothing

Section 68 proved the nullity detector's `(d=2, D=5)` box has an exact blind spot at degree
`>= 6`. The obvious follow-up -- re-run every `0,0,0` at a wider box -- could have flipped a
landed claim. It did not. **What it flipped instead was a calibrator, and that turned out to
be an artefact I nearly reported as a result.**

### 69.1 The box has to be screened before it can screen anything

Reading `nullity()`: unknowns are `(d+1)(D+1)` polynomial coefficients plus `Dq + 1` for the
right-hand side, with `Dq = D + 6` by default, against `M + 1 = 161` equations. So at
`d = 2` the system is overdetermined exactly while `4D + 10 < 161`:

| `D` | unknowns | equations | vacuous? |
|---|---|---|---|
| 5 | 30 | 161 | no |
| 12 | 58 | 161 | no |
| 37 | 158 | 161 | no |
| **38** | **162** | 161 | **YES -- every input fires** |

**At `d = 2`, `M = 160`, any `D >= 38` returns nullity `> 0` for EVERY input, vacuously.**
`D = 12` is comfortably safe. That is T40 applied to the instrument rather than to a claim:
compute what the box could possibly return before reading anything out of it.

Two live controls, both run at `D = 12`:

- **POWER.** `6N`, `8N`, `12N` must fire, since `1 - x^d` has degree `d <= 12`. They do:
  `[15,8,7]`, `[10,5,5]`, `[2,1,14]`, against `[0,0,0]`, `[0,0,0]`, `[0,0,6]` at `D = 5`.
- **NEGATIVE.** Random sets at densities `0.10`, `0.33`, `0.50` must NOT fire. They do not --
  `[0,0,0]` at both boxes. **The widened box is not over-parameterised.**

### 69.2 The targets: no flip

| set | `D = 5` | `D = 12` | verdict |
|---|---|---|---|
| primes | `0,0,0` | **`0,0,0`** | non-adapted survives |
| `A*` | `0,0,0` | **`0,0,0`** | **BOX-ONLY row SURVIVES** |

**`A*`'s ledger row does not change.** It stays BOX-ONLY, but it is now BOX-ONLY over a box
more than twice as wide, with a passing negative control and a demonstrated power check --
materially stronger evidence than it had, and the outcome the capture was written to test
for. The `A*` ledger stands at FOUR PROVEN / one BOX-ONLY / one MEASURED-IN-RANGE in all
three copies; nothing to propagate.

### 69.3 The calibrator fired, and the fire is empty

`{2^(2^k)}` read `0,0,0` at `D = 5` and **`3,3,3` at `D = 12`**. Taken at face value that
flips the corpus's own non-adaptation calibrator. **It is an artefact.**

The detector reads only `m <= M`. At `M = 160` the set `{2^(2^k)}` truncates to `{2, 4, 16}`
-- 256 is outside the window -- so `Y` is a POLYNOMIAL of degree 16. With `Dq = D + 6 = 18`,
the assignment `p_0 = 1`, `q = Y` is an exact solution. **The "relation" is `Y = Y`.**

Predicted before running: move 256 into the window and the fire must stop.

| set | `Dq` | `deg Y` | nullity | `deg Y <= Dq`? |
|---|---|---|---|---|
| `{2,4,16}` | 18 | 16 | **`3,3,3`** | **yes** |
| `{2,4,16,256}` | 18 | 256 | `0,0,0` | no |
| `{2,4,16}` | 11 | 16 | `0,0,0` | no |
| `{2,4,16,256}` | 11 | 256 | `0,0,0` | no |

**The `deg Y <= Dq` column predicts fire and no-fire exactly, four for four.** So
`{2^(2^k)}` is not adapted; the detector was reporting the trivial solution available to any
set whose truncated support is short enough.

**Two consequences.** First, **any finite -- or window-truncated -- support fires vacuously
once `Dq >= deg Y`**, which is a second blind spot of the instrument, opposite in sign to
section 68's. Second, **the corpus's `{2^(2^k)}` calibrator reads `0,0,0` at `D = 5` for a
reason that is a window coincidence** (`deg Y = 16 > Dq = 11`), not robustness. Its verdict
is CORRECT -- with `M = 400` it reads `0,0,0` at both boxes -- but **`M` must be pinned
explicitly whenever that row is quoted.** The same caution applies to T31b's greedy-support
rows, which are finite prefixes by construction.

### 69.4 What I would have reported without the check

Without the `deg Y <= Dq` diagnosis this section would have said "`{2^(2^k)}` is base-adapted
at `D = 12`, flipping a landed calibrator". That is false, and it would have propagated into
section 7's witness, which leans on that calibrator firing nowhere. **The negative control
passed, so the box was sound; the artefact was in the SET, not the box** -- a distinction the
random-set control could not have caught, because random sets are dense and never truncate
short. **A control screens the failure mode it was designed for and no other.**

**Status.** The probe ran at double width with both controls live. `A*` and primes survive
unchanged, on materially stronger evidence. One calibrator fire diagnosed as a trivial
solution and refuted four for four. One new instrument blind spot characterised
(`Dq >= deg Y` fires on nothing) and one vacuity ceiling stated exactly (`D >= 38` at
`M = 160`). No landed claim flipped. Receipt:
`state/formal_math/erdos257_period_noncollapse/box_widening_receipt.json`.

## 70. The third artefact: an under-fed top shift -- and my own note found it first

Section 69 predicted a third artefact mode in the nullity detector and set this section up to
"correct T31b's greedy-support rows at source". **That instruction was wrong. There is
nothing to correct, because this lane already found it -- with a better experiment than the
one I planned.**

### 70.1 What was already on disk

The realised-support check in the section 8-11 range carries the whole finding:

| target | k=2 | k=3 | k=4 at `M=160` | `M=240` | `M=320` | `M=390` |
|---|---|---|---|---|---|---|
| `3/(2^13 - 1)` | 0 | 0 | **6** | **0** | 0 | 0 |
| `1/1009` | 0 | 0 | **5** | **0** | 0 | 0 |

and states outright: *"The two nonzero entries at `M = 160` are **window artifacts**: a
relation can hold across a short prefix without holding on the sequence, and both collapse to
`0` as soon as more coefficient equations are imposed. The control discriminates exactly as it
should -- Thue-Morse stays at `5` for every `M` in `160..390`, because its relation is
genuine."*

**A four-point `M` sweep AND a genuine-relation control.** That is a better-designed probe
than the single-box check section 69 proposed. **T13/T29a, tenth payoff in twelve iterations**
-- and this time what was already on disk was not just the answer but a stronger method.

**T31b's blast radius is zero**: it cites the greedy supports of `1/21`, `4/9`, `3/(2^7-1)`,
whose smallest elements are `5`, `2`, `6` -- all correctly `0,0,0`. The two artefact rows
appear only in the table above, correctly labelled. **No landed claim is wrong.**

### 70.2 What is actually new: the mechanism, and a formula that replaces the sweep

The note knew THAT these were window artefacts and how to DETECT them -- grow `M` until they
collapse. It did not say WHY, and the why gives a predictor.

Reading the index arithmetic in `nullity()`: block `i` contributes to row `m` only when
`(m - e) % k^i == 0`, so **block `i` is fed from just the coefficient positions
`j <= M / k^i`**. At `k = 4, d = 2` the top block is `Y(x^16)`, fed from `j <= 160/16 = 10`.
Column `e` of that block is live iff some support element `j` satisfies `k^d j + e <= M`.
Hence, with `s = min(support)`,

> **free columns  =  #{ e in 0..D : k^d * s + e > M }.**

For `k = 4, D = 5, M = 160`: `s <= 9` gives 0, **`s = 10` gives exactly 5** (only `e = 0`
survives, at `m = 160`), and `s >= 11` gives 6.

| target | `min(supp)` | `k=4` at `M=160` | predicted |
|---|---|---|---|
| `1/21` | 5 | 0 | 0 |
| `4/9` | 2 | 0 | 0 |
| `3/(2^7-1)` | 6 | 0 | 0 |
| `3/(2^13-1)` | **12** | **6** | **6** |
| `1/1009` | **10** | **5** | **5** |

Five for five, and the `s = 10 -> 5` case is a knife edge only the exact arithmetic produces.
**Run against the note's whole sweep, the formula predicts all twelve cells** -- `M = 160`,
`240`, `320`, `390` for `3/(2^13-1)`, `1/1009` and `1/21`.

**So the note's procedural rule upgrades to a closed form:** instead of "a nullity verdict on
a finite prefix is meaningless until shown stable under a growing window", one can now
compute `min(support)` against `M / k^d` and know the verdict before running anything. **The
top shift is decorative unless `M >= k^d * (min(support) + D)`.**

### 70.3 A prediction I got wrong, caught before the run

Section 69's payload predicted `nullity = 6 - (#elements <= 10)`. That is wrong: one small
element makes ALL six columns live, not one. The dependence is on `min(support)` alone, not on
a count. **Reading the index arithmetic corrected it before the run rather than after** --
twenty-first wrong prediction on record, and the first caught pre-run by reading the code
instead of the output.

### 70.4 Three artefact modes, all distinct

The detector now has three characterised failure modes, and they do not overlap:

| trap | condition | effect |
|---|---|---|
| **T47** | true relation needs degree `> D` | **LOSES** real relations (witness `6N`) |
| **T48** | `Dq >= deg Y` on the truncated support | **INVENTS** relations (witness `{2^(2^k)}`) |
| **T49** | `k^d * min(support) > M` | **INVENTS** relations (witness `1/1009`) |

**T48 and T49 both invent, but a control for one cannot catch the other**: T48 needs a short
truncated support, T49 needs no SMALL elements, and a set can have either without the other.
That is T48d again -- a control screens the failure mode it models and no other.

**Status.** The target was already answered on disk, by a better experiment, and the
instruction to correct landed rows was wrong -- stated plainly rather than quietly dropped.
What is new is the mechanism and a closed-form predictor validated on twelve cells of the
note's own table, plus a third named artefact mode and one wrong prediction caught before it
cost a run. Receipt:
`state/formal_math/erdos257_period_noncollapse/underfed_shift_receipt.json`.

## 71. The `tau_E = 1` discriminator is REFUTED as sufficient -- death also arrives at 3, 5, 7

Section 67 found that the `tau_E = 1` density separates its nine families cleanly -- `0.000`
for both survivors, `0.10`-`0.33` for every killer -- and T46a records it as **the**
discriminator. **It is not sufficient, and one construction settles it.**

### 71.1 The construction, and its algebra

Take **`E = {4} u {4p : p prime} = 4 * ({1} u P)`**. Every element is a multiple of 4, so
`tau_E(m) = 0` whenever `4 !| m`. For `m = 4k`: `4 | 4k` always, and `4p | 4k` exactly when
`p | k`. Hence

> **`tau_E(4k) = 1 + omega(k)`.**

Two consequences fall straight out. First, `{tau_E = 1} = {4k : omega(k) = 0} = {4}` -- **a
single point**, so the `tau_E = 1` density is `1/HI`, indistinguishable from section 67's
survivors. Second, `Odd_E = {4k : omega(k) EVEN}` -- a rescaled `omega`-parity set, which is
parity-dense.

Spot-checked against the definition: `k = 1, 2, 6, 30, 210` give `omega = 0,1,2,3,4` and
`tau_E(4k) = 1,2,3,4,5`. Exact.

### 71.2 Same discriminator value, opposite verdicts

| `E` | `{tau_E = 1}` | maxgap `Odd_E` at `HI = 25k / 50k / 100k / 200k / 400k` | socket |
|---|---|---|---|
| `{4} u {4p}` | **one point** | `52, 76, 76, 76, 76` -- **plateaus** | **KILLS** |
| `4N` (s67 survivor) | **one point** | `628, 884, 1260, 1780, 2524` -- **grows** | survives |
| model `8*sqrt(HI/4)` | -- | `632, 894, 1265, 1789, 2530` | -- |

`4N` tracks the square-root model to within **0.3% at every point**; the new `E` does not move
at all across an eightfold window increase. **Identical `tau_E = 1` density, opposite
verdicts.** T46a's criterion separates the families section 67 happened to test; it is not the
invariant.

**Death arrives through `tau_E = 3, 5, 7, ...`** -- the higher odd values, which section 67
never considered because every family it tested had its odd mass concentrated at 1.

### 71.3 What the invariant actually is

Restrict `tau_E` to `min(E) * N` and ask what FUNCTION it is:

- `E = 4N` gives `tau_E(4k) = d(k)`, odd exactly at squares -- **parity-SPARSE**, gaps
  `~8 sqrt(HI/4)`, socket survives.
- `E = 4*({1} u P)` gives `tau_E(4k) = 1 + omega(k)`, odd for half of all `k` --
  **parity-DENSE**, bounded gaps, socket kills.

**The invariant is the parity structure of `tau_E` on `min(E) * N`, not a density at any one
value.** That is strictly sharper than "dense in a progression", and it reframes the open
question (B): non-syndetic `Odd_E` requires the parity of `tau_E` on `e1 N` to be
**square-like rather than omega-like**. Whether that forces `E` into a solved class remains
open -- this section refutes the MECHANISM section 67 offered for (B), not its conclusion.

### 71.4 A threshold of mine that was arbitrary, and what caught it

The probe's verdict column labelled anything with `maxgap <= 64` as KILLS. The new `E` reads
`76` at one window and was therefore printed as "survives" -- **wrong, and wrong because the
threshold was invented rather than derived.** What caught it was this lane's own standing
rule: *never read a scalar at one `M` as a limit*. The growth test, not the number, decides:
`76` that does not move under an eightfold window is bounded; `972` that tracks `sqrt` is not.
**Twenty-second wrong call on record, caught by an existing rule rather than by luck.**

**Status.** One landed criterion refuted as sufficient, by construction rather than by
measurement, with the algebra exact and spot-checked. One sharper invariant identified -- the
parity structure of `tau_E` on `min(E) * N`. Open question (B) reframed but NOT answered, and
its section-67 mechanism withdrawn. Receipt:
`state/formal_math/erdos257_period_noncollapse/omega_parity_counterexample_receipt.json`.

## 72. NEGATIVE: the conjecture is false, and section 5d proved it before I asked

**This iteration produced no new mathematics.** It set out to attack "sparse `Odd_S` implies
`S` is essentially a union of arithmetic progressions", which would have closed the complement
family. **The conjecture is FALSE, and the refutation was already on disk in my own
directory** -- stronger, with a closed form I did not have, and verified over a range 3.3
times larger than mine.

### 72.1 What section 5d already says

`ErdosProblems/Erdos257/SupportWordStructureLab.md` section 5d, titled **"Characteristic two:
the divisor layer alone cannot obstruct"**:

> *"Over `F_2` the Dirichlet inverse of `1` is `mu`, which reduces to the squarefree indicator,
> and **every** value of `g * mu` already lies in `{0,1}`. Hence for **any** eventually
> periodic `g` the set `A_g = {n : (g * mu)(n) = 1}` satisfies
> `sum_{a in A_g} 1/(t^a - 1) = sum_n g(n) t^{-n}` in `F_2(t)`. The simplest witness is
> `g = delta_1`, giving **`A` = the squarefree numbers**, `f_A(n) = 2^{omega(n)} = 0 (mod 2)`
> for every `n >= 2` ... Verified for all `n <= 2 x 10^5`."*

That is the entire content of what I derived this turn, in a **more general form** -- any
eventually periodic `g`, not just the sparse target I happened to pick -- and with the closed
form **`tau_squarefree(n) = 2^{omega(n)}`**, which PROVES evenness for `n >= 2` where my run
only measured it. I confirmed the closed form independently (every `n <= 60000`, zero
violations), which is exactly the wrong way round: **the proof was already there and I
produced a measurement of it.**

**T13/T29a, twelfth payoff, and the most complete yet.** Not merely the answer -- a stronger
theorem, a larger verification range, and the closed form I lacked.

### 72.2 The process failure, precisely

Cross-index line 69 carries the row *"characteristic-two no-go;
`sum_{a squarefree} 1/(t^a - 1) = 1/t` in `F_2((1/t))` | same, section 5d"*. **I read that row
this turn -- in the novelty sweep -- and only followed it AFTER deriving the same construction
from scratch.** The sweep found `squarefree` at 4 hits in the note and 4 in the cross-index; I
read the note's hits, saw the `mu`-inversion, and went ahead rather than opening section 5d
first. **The pointer was in the index, in the right row, with the right formula, and I walked
past it.**

### 72.3 The one thing that reframes six sections

Section 5d's TITLE is the finding: **the divisor layer alone cannot obstruct.** Sections
66-71 -- the socket criterion, the sparsity inversion, both-exits-are-solved, the
`tau_E = 1` refutation -- all live inside that layer. They are sharp results about a layer
already known to be insufficient.

Concretely: section 66 reduced socket death to syndeticity of `Odd_E`, and section 71 showed
the parity map is a bijection, so **every sparse target has exactly one preimage** and
socket-survivors are as abundant as sparse sets. Section 5d says the same thing in the
characteristic-two model and draws the conclusion I had not: **no amount of sharpening inside
the divisor layer will produce an obstruction.** My own note said the local version at the
`F_2` bijection -- *"a reparametrisation, not a filter"* -- and I did not connect it to the
socket lane until now.

**Consequence for routing: any real progress needs something OUTSIDE the divisor layer.**
That is the one durable output of this section, and it is a navigational result, not a
mathematical one.

### 72.4 What I checked anyway, and what little may be mine

`A = {squarefree numbers}` passes four gates: socket survives (`Odd_A = {1}` exactly),
reciprocal-divergent, nullity `0,0,0` at BOTH `D = 5` and `D = 12` with both artefact screens
passing (`deg Y = 399 > Dq`; `min(support) = 1`, top shift fed) and the `N` calibrator
returning `14,9,8` in the same run. **None of this is news** -- and residual (m) already
records that the primes are an open-class member, so open-class members were never scarce
either.

The only piece I cannot find already stated: **the squarefree SET is not eventually periodic
because its density `6/pi^2` is IRRATIONAL** (measured `0.607905` at `2 x 10^5` against
`0.607927`), and eventually periodic sets have rational density. Section 5d discusses eventual
periodicity of `f_A`, which is a different object. That is a small observation and I am not
inflating it.

**Status. NEGATIVE ITERATION.** One conjecture refuted, by a landed section that predates it.
No new mathematics. One navigational finding that reframes sections 66-71 as work inside a
layer proved insufficient. One process failure named exactly: the cross-index pointed at the
answer and I derived it from scratch instead. Receipt:
`state/formal_math/erdos257_period_noncollapse/squarefree_candidate_receipt.json`.

## 73. NEGATIVE: the carry lane was closed too -- by section 19, and the reading found it in three steps

Section 72 concluded that the divisor layer cannot obstruct and routed here: **go outside it,
to the carries.** **The carry lane is also closed, by my own section 19, and this time the
reading found it before a single line of derivation was run.**

### 73.1 T51b applied, and it worked

Section 72's failure was deriving before following a cross-index pointer. This section
inverted that order deliberately. The carry sweep returned **42 hits in the note, 22 in the
cross-index, 22 in `SupportWordStructureLab.md`, 19 (plus 7 `borrow`) in the untracked
`CrossRepresentationInformationLossMap.md`** -- roughly a hundred. The carry layer is not
unexplored; it is one of the most worked parts of the corpus, carrying **two Lean theorems**
(`irrational_erdosSupportSeries_of_weighted_coeff_carry_certificates`,
`..._of_sunflower_forcedCarry_supply`) and five dedicated notes including an explicit
`SourceClockBorrowNoGo.md`.

Following the cross-index rows rather than the note text led in three steps -- index -> T18 ->
section 18 -> section 19 -- to the closure. **Zero computation, zero false claims.** That is
T51b working as intended, and it is the difference between this section and section 72.

### 73.2 The open item, and why it is not open

T18 names it precisely: *"M8's forcing half is NOT covered and remains open"*, sharpest at the
primes, where `d(p) = 2` forces `tau_A(p) = 1_A(p)` and the carry reads
`Q_p = 2 Q_{p-1} + t_p - 1_A(p)` -- *"nearly doubling, payable down by at most 1"*. Section 18
adds that the substance is an **arithmetic forcing** hope, not a signal claim, and that
*"that half is untouched"*.

**Section 19 then closes it.** From `Q_n = 2 Q_{n-1} + t_n - tau_A(n)` with `Q_n >= 0` and the
ceiling `tau_A(n) <= d(n) - 1`:

    Q_N  >=  sum_{n=1..N} 2^(N-n) ( t_n + 1 - d(n) )
    0    >=  y + 1 - sum_n d(n) / 2^n,     sum_n d(n)/2^n = E = 1.6066951524152917
    ==>  y  <=  E - 1  =  T_1  =  0.6066951524152918.

And that is **vacuous** -- immediate from `1 not in A`, since `y = sum_{a >= 2} z_a <= T_1`.
The ceiling, aggregated, carries no information beyond the hypothesis that introduced it.

**The closure is general, and it covers exactly the prime route T18 pointed at:**

> *"Every way of summing the ceiling -- over all `n`, over the primes only, over any index set
> with any weights -- produces an UPPER BOUND on `y`, because the recursion is LINEAR in
> `tau_A` and `y` is its generating value. But `y` is a free parameter ranging over
> `(0, T_1)`. An upper bound on a free parameter is never a contradiction. So no aggregated
> form of M8 can close."*

I had formed the candidate inequality `Q_{n-1} <= (B + d(n) - 1)/2` -- the same linear
relation, restricted at primes to `Q_{p-1} <= (B+1)/2` -- before opening section 19. **It is
an instance of exactly what section 19 rules out.** Following the pointer cost one read and
saved the derivation entirely.

### 73.3 Two lanes, both closed by my own prior sections

| lane | closed by | where |
|---|---|---|
| divisor layer | `SupportWordStructureLab.md` section 5d | section 72 |
| carry, aggregate | `CertificateSocketCollapse.md` section 19 | this section |

**Thirteenth T13/T29a payoff, and the third consecutive total one.** Sections 66-71 worked
inside the divisor layer; section 72 routed to the carries; the carries' aggregate route was
closed twenty-odd sections before either.

### 73.4 The surviving sliver, stated narrowly

Section 19 closes every **LINEAR** functional of the ceiling -- that is what "linear in
`tau_A`, and `y` is its generating value" delivers. **What it does not address is a NON-LINEAR
use of the ceiling**: a forcing that combines `tau_A(n) <= d(n) - 1` with itself at several
ranks multiplicatively, or through a quantity that is not a weighted sum of `tau_A`.

That is a genuinely narrower residual than "the carry layer", and I am not claiming it is
promising -- only that section 19's proof does not reach it. **Anything of the form
"sum/average the ceiling over some clever index set" is dead, including every variant I can
presently name.**

**Status. NEGATIVE ITERATION, no computation run.** One routing hypothesis from section 72
tested and closed. One open item located exactly (T18's forcing half) and found already
answered (section 19), with the closure general enough to cover the prime-restricted form it
was sharpest on. One residual narrowed from a layer to a single word: non-linear. **The method
worked this time -- pointer before derivation -- and that is the only thing separating this
section from section 72.** Receipt:
`state/formal_math/erdos257_period_noncollapse/carry_lane_closed_receipt.json`.

## 74. The Lean sweep is a GREEN LIGHT -- and the build is deferred, not passed

Three iterations in a row proposed lanes the corpus had already worked. This one switched to
construction, and construction turned out to be genuinely unbuilt. **The sweep is the
positive result; the build did not run and I am not claiming it.**

### 74.1 Step 0: the sweep, with a near-miss that nearly inverted it

Swept the 9,771-file Lean corpus for the objects section 66 needs:

| symbol | files |
|---|---|
| `divisorCount` | **0** |
| `tauA` | **0** |
| `IsSquare` | **0** |
| `supportCoeff_complement` | **0** |
| `supportCoeff` | 53 |
| `Mobius` / `mobius` | 45 / 27 |
| `binaryCoeffTail` (calibrator) | 22 |

**The first run of this sweep returned 0 for EVERY pattern, including ones that exist.** The
cause: `--include=*.lean` unquoted, which zsh glob-expanded before `grep` saw it, so the
command errored out (`no matches found: --include=*.lean`) and never searched. **I nearly
read that as "nothing is formalised", which would have been exactly backwards on the terms
that DO exist.** What caught it was the error line plus adding `binaryCoeffTail` as a
calibrator -- a term I knew was present, which must return non-zero or the sweep is broken.
**Every corpus sweep needs a known-present calibrator in the same run**, for the same reason
every measurement does.

### 74.2 What the corpus already has, and what it does not

`CertificateKernel.lean:9044` already carries the exact object, with the exact reading:

> *"**The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}` -- the Dirichlet incidence
> `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually
> stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give
> `ω`; prime powers give `Ω`."*
>
>     noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
>       (n.divisors.filter fun d => d ∈ A).card

So the base object is landed and is precisely section 66's `tau_A`. **What is absent is the
complement identity** -- `supportCoeff_complement` returns zero files, and no
`supportCoeff.*compl` pattern appears anywhere. **Section 66's pointwise foundation is not
formalised.** After three negative iterations, that is a green light.

### 74.3 The statement, written and NOT verified

    theorem supportCoeff_add_supportCoeff_compl (A : Set ℕ) (n : ℕ) :
        supportCoeff A n + supportCoeff Aᶜ n = n.divisors.card

-- every divisor of `n` is counted exactly once, on one side or the other. In mathlib terms
this should be `Finset.filter_card_add_filter_neg_card_eq_card` after `Set.mem_compl_iff`.

**The build returned `rc = 75` -- REFUSED TO RUN, not failed.** Another owner holds the
project-build lease `lean-project-build:formal_math/erdos257_period_noncollapse`. The guard's
own payload marks itself **`proof_scope: not_proof_evidence`** and forbids
`attached_capacity_wait`, `retry_loop`, `ticket_polling` and `raw_lake_bypass`.

**So the theorem is UNPROVEN and unclaimed.** Per T26a the file was saved as a patch and
removed from the project rather than left uncompiled under a foreign lease. Durable handles
for re-entry:

| field | value |
|---|---|
| ticket | `rct_926e0262a7cfc96f9afb` |
| run id | `cmdrun_20260823T041235Z_66574_e9bd590766ee` |
| conflict key | `lean-project-build:formal_math/erdos257_period_noncollapse` |
| re-entry condition | no active owner holds that key |
| patch | scratchpad `SupportCoeffComplement.lean.patch`, 1341 bytes |

### 74.4 A carried memory that was stale

My carried state said the warm-Mathlib premise had expired -- "643M, 1 olean". **It has not.**
This project has **8,426 oleans, 8.7 GB of `.lake`, toolchain `v4.29.1`, 37 GiB free**, and
`CertificateKernel.olean` is built at 25 MB. A Lean build here is cheap, and the only thing
standing between this lemma and a captured `rc = 0` is the project-build lease. **The stale
memory would have argued against attempting Lean at all.**

### 74.5 The standing caveat, restated

Cross-index T51: this identity lives inside the DIVISOR LAYER, which section 5d proves cannot
obstruct Erdős 257 alone. **Formalising it is certified infrastructure, not progress on the
problem**, and the file's own docstring says so. It is worth landing because section 66's
whole chain rests on it and nothing beneath that chain is currently machine-checked.

**Status.** Sweep run and calibrated: the s66 foundation is genuinely unformalised -- the
first non-negative finding in three iterations. One theorem written, **build DEFERRED at
`rc = 75` under a foreign lease and explicitly NOT claimed**, with ticket, run id, conflict
key and re-entry condition recorded. One near-miss caught by a calibrator. One stale carried
memory corrected against the live tree.

## 75. PROVEN: the complement identity is machine-checked -- and s66's second pillar is still bare

The build that section 74 deferred at `rc = 75` ran this iteration and returned a **captured
`rc = 0`**. The lease had cleared: no `lake build` or `lean_fast_build` process was alive, and
the previous holder's work had landed as `cd9a158373` and `833064175b`. Their three files are
still dirty, which is why section 74 read the lease as held -- **dirty files are not a lease.
A lease is held by a running command.** That misreading cost one iteration.

### 75.1 The theorem

```lean
theorem supportCoeff_add_supportCoeff_compl (A : Set N) (n : N) :
    supportCoeff A n + supportCoeff (A^c) n = n.divisors.card
```

`Erdos257PeriodNoncollapse/SupportCoeffComplement.lean`. Build receipt, captured, twice:

```
[2880/2880] Built Erdos257PeriodNoncollapse.SupportCoeffComplement (19s)
lean-fast-build: Erdos257PeriodNoncollapse.SupportCoeffComplement -> 0 (29.6s)
Build completed successfully (2880 jobs).
```

Axioms, namespace-qualified, emitted in-file per the corpus convention:

```
'Erdos257PeriodNoncollapse.supportCoeff_add_supportCoeff_compl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

The standard three. **No `sorryAx`.** This is the pointwise fact `tau_A = d - tau_E` on which
section 66 rests, in the additive form that avoids natural subtraction.

### 75.2 The name in my own patch was deprecated

The saved patch closed the goal with `Finset.filter_card_add_filter_neg_card_eq_card`. Grepping
Mathlib before building -- rather than after a failure -- showed why that would have been a
mistake worth a whole build cycle:

```
Mathlib/Data/Finset/Card.lean:637:
  @[deprecated (since := "2025-12-12")]
  alias filter_card_add_filter_neg_card_eq_card := card_filter_add_card_filter_not
```

It is an **alias, not a theorem**, and a deprecated one. The live name is
`Finset.card_filter_add_card_filter_not`, with `p` explicit and `s` implicit. Swapping it in
before the build is why the first attempt was also the last. **Grep the target name in the
dependency, not only in your own corpus, and read whether what you found is a theorem or an
alias.**

### 75.3 The finding: section 66's SECOND pillar is unformalised in both places

Section 66 is a conjunction of two facts, not one:

  (P1)  `tau_A + tau_E = d` pointwise            -- **now machine-checked, this section**
  (P2)  `d(m)` is odd exactly when `m` is a square -- **still bare**

Only (P1) plus F2-linearity gives `Odd_A = Sq XOR Odd_E`; without (P2) the `Sq` term has no
content. Two calibrated sweeps this iteration:

| target | Mathlib | corpus lib | calibrator in same run |
|---|---|---|---|
| divisor-count-odd-iff-square, under every name tried | 0 | 0 | `Nat.card_divisors` = 2 files |
| `IsSquare` anywhere | -- | **0 files** | `supportCoeff` = 53 files |

The `supportCoeff` calibrator returning exactly **53**, the same count section 74 measured,
is what certifies the sweep actually ran. **`IsSquare` does not appear anywhere in this
project's Lean library.** Mathlib has the involution machinery -- `image_div_divisors_eq_divisors`
at `Mathlib/NumberTheory/Divisors.lean:562` -- but not the parity conclusion.

So section 66 is now **exactly half certified**, and the uncertified half is the half that
carries the arithmetic. (P2) is classical and the proof is the `d -> n/d` pairing with fixed
points at `sqrt n`, but it is a real formalisation job, not a one-liner, and nothing on disk
starts it.

### 75.4 A near-miss, recorded

One sweep in this iteration **errored instead of running**: `ugrep: error at position 18`,
an unescaped `\)` inside an alternation. It printed nothing. Its calibrator printed 5 files,
which is the only reason the empty result was read as a broken pattern rather than as an
absence. This is T53a in a second costume: **last iteration a glob ate the flag, this
iteration a regex ate the pattern. The defect class is "a search that did not run looks
exactly like a search that found nothing."** The calibrator caught both.

### 75.6 The F2-linearity pillar is ALSO proven -- and (P2) turns out not to be needed for it

Naming (P2) as "the next target" was right about the gap and wrong about its position. The
decomposition is finer than section 66's prose suggests. What section 66 *consumes* pointwise
is a XOR relation among three parities, and that relation follows from (P1) by parity
arithmetic alone -- **the square theory is only the classical NAME of the third parity, not a
premise of the linearity.** Isolating that gave a second theorem in the same window:

```lean
theorem supportCoeff_odd_xor (A : Set N) (n : N) :
    ((Odd (supportCoeff A n) <-> not (Odd (supportCoeff (A^c) n))) <-> Odd n.divisors.card)
```

Proof, entire: `have h := supportCoeff_add_supportCoeff_compl A n; simp only [Nat.odd_iff]; omega`.
`omega` closes an iff-of-iffs over `% 2` atoms once the additive identity is in context -- the
whole `F2`-linearity step is one linear-arithmetic goal. Captured `rc = 0`,
`Built Erdos257PeriodNoncollapse.SupportCoeffComplement (20s)`, axioms
`[propext, Classical.choice, Quot.sound]`. No `sorryAx`.

**So the correct ledger for section 66 is three parts, not two:**

| part | content | status |
|---|---|---|
| (P1) | `tau_A + tau_E = d` pointwise | **PROVEN** |
| (P1.5) | `Odd_A XOR Odd_E = Odd(d)` -- the `F2`-linearity | **PROVEN** |
| (P2) | `Odd (d n)` iff `n` is a square -- the name `Sq` | **bare, and now purely classical** |

The mathematical content of the socket criterion is (P1) and (P1.5), and both are now
machine-checked. (P2) is a textbook fact that supplies a *label*: it says the third parity
class is the squares. Its absence no longer blocks the criterion; it blocks only the
sentence "`Sq`" being a checked synonym for "`Odd(d)`".

**Why (P2) is still a real job.** Mathlib has `Nat.card_divisors` in product form
(`ArithmeticFunction/Misc.lean:222`) and `Prime.dvd_finset_prod_iff`, so "odd product iff all
factors odd" is reachable. The missing piece is `IsSquare n` iff every exponent of
`n.factorization` is even, which Mathlib does not carry. Its forward direction is
`Nat.factorization_mul`; its converse needs `r` rebuilt as
`n.factorization.prod fun p k => p^(k/2)` and `Nat.factorization_prod_pow_eq_self`. That is a
hundred-line job, not a window job, and it is captured rather than started.

### 75.5 The standing caveat, unchanged

Cross-index T51: this lives in the DIVISOR LAYER, which section 5d proves cannot obstruct
Erdos 257 on its own. **This is certified infrastructure, not progress on the problem.** It
is worth having because section 66's chain rested on an unchecked pointwise claim and now
rests on a checked one.

**Status.** TWO theorems PROVEN with captured `rc = 0` and clean axioms. One deprecated name
caught before it cost a cycle. One structural finding: **(P2) is unformalised in Mathlib and
absent from this corpus**, which names the next Lean target precisely. One near-miss recorded.
The lease-reading error from section 74 is corrected at source: dirty files are not a lease.

## 76. NEGATIVE, and the negative lands on me: there is no "third layer", and the socket is a bounded-window argument

I set out to answer "what obstructs outside the divisor layer (T51) and the carry-aggregate
layer (T52)?" The question is **malformed**, and the file that says so has been on disk since
2026-08-21: `Erdos257ResearchFrontierCloseout.md`, which I had never opened.

### 76.1 The two "layers" are the two terms of one equation

Its section "What all serious surviving routes now share" states the transport law
`Q_n = 2 Q_{n-1} + t_n - f_b(n)` with `f_b(n) = sum_{d | n} b_d`, and then, verbatim:

> "The dyadic/cylinder side asks whether a short suffix interval crosses a moving binary
> boundary. The arithmetic side asks whether the proper-divisor pulses in `f_b(n)` place the
> carry in exactly that interval. **These are not two obstructions. They are the two terms of
> (2).**"

So T51 and T52 were never two independent closed layers with a gap between them. They are
`f_b(n)` and `Q_n` -- the two terms of a single law. **Asking what lives "outside both" is
asking what lives outside an equation.** My own framing had been generating the question for
four iterations. Corrected here and at T55.

### 76.2 The census already exists, and the "neither" bucket is empty for a structural reason

The closeout counts **25 distinct mechanism families** under an explicit rule: *"Changing a
rational target, strengthening a finite audit, or restating the same fatal seam in another
normalization does not create a new route."* Its 2026-08-22 reconciliation then classified
"more than two dozen additional attack and representation notes, one attempted private Lean
module, and a strengthened private `4/9` module" -- and concluded **"The mechanism-family count
remains twenty-five."**

The bucket is empty because the counting rule collapses representation changes onto the
residual they re-describe. That is not an absence of imagination in the corpus; it is a
theorem about the corpus's own admission rule.

### 76.3 The sharpest instance: a genuinely carry-free criterion that returns the carry

`SupportWordStructureLab.md` section 5b -- also unread by me until this iteration -- derives an
equivalent form of the problem with no dynamics in it:

> **Erdos 257 iff for every infinite `A` and every `l >= 1`, `Lambda(l,A) not in Z[1/2]`**,
> where `Lambda(l,A) = sum_{a in A} (2^{l mod a} - 1)/(2^a - 1)`.

Its own text: *"No carry, no cylinder, no reservoir, no dyadic seam appears: the entire
problem is that a convergent sum of explicit rationals is never an integer."* This is the best
"neither" candidate the corpus has -- carry-free **by construction**.

And it is closed in the same section. Expanding with `j_a(l) = a - (l mod a)` recovers
`sum_{j>=1} f_A(l+j) 2^{-j}`, which is `Q_l`; on the progression `Lambda(k*l_0, A) = Qtilde_{k*l_0}`.
The section's own words: *"The carry-free route and the carry route return literally the same
number"*, and *"this is not a new route: it is the same residual in another normalisation, and
it produces no one-way theorem by itself."*

**A coordinate built specifically to have no carry in it computes the carry.** That is much
stronger evidence than a failed search: it says the barrier is intrinsic rather than an
artefact of the coordinate it was met in, which is what section 5b concludes too.

### 76.4 The finding I did not want: section 66 is a bounded-window argument

The closeout lists five proof shapes for which **the corpus already contains exact
countermodels**: a bounded window of divisor loads; a fixed collection of 2-adic or
primitive-prime coordinates; scalar residual mass, denominator height, support count, or
phase; local ownership without the complete rank-one history; an eventually periodic or
finite-state carry rule. Of the countermodels it says they *"can reproduce an arbitrarily long
dangerous suffix together with all local divisor congruences. They fail only at reachability
from the actual initial state and its complete Boolean ancestry."*

Section 66's socket kills `A = N \ E` **iff `Odd_E` is syndetic** -- iff the odd-parity divisor
set has bounded gaps. A bounded gap `g` is exactly the statement that every window of length
`g` carries an odd divisor load. **That is the first forbidden shape, verbatim.**

I checked whether anyone had already classified it. `syndetic` appears in **exactly one file in
the entire Erdos 257 directory: this one** (calibrators in the same run: `boundary` = 14 hits in
the closeout, 15 files mention `socket`). The closeout's own uses of "socket" are its three
consumers of the missing law, an unrelated sense. **So the socket criterion was never
classified against the 25 families, and classifying it puts it inside a class with exact
countermodels on disk.**

This does not retract section 66. The criterion is correct and (P1)+(P1.5) are machine-checked.
It relocates it: **the socket is a sufficient killer, not a route to the theorem**, because its
sufficient condition is precisely the regime the countermodels evade. Consistent with honest
residual (b), `maxgap(Odd_primes) = 20` -- bounded in range -- while the open case is exactly
unbounded gaps. **Falsifier for this classification:** if the socket's kill condition can be
rewritten to consume the complete Boolean ancestry rather than a bounded window, it escapes the
class. I have not shown that it cannot; I have shown that as stated, it does not.

### 76.5 Provenance of the bar I have been working to

The operator's progress criterion is not a paraphrase; it is this file's
"Research-allocation guard", nearly verbatim:

> "A reopened route must supply at least one genuinely new producer: a one-way theorem from the
> actual initial state that uses the complete Boolean/divisor ancestry (or proves why a smaller
> state is sufficient) and **forces a cofinal return, excludes the boundary mode, or constructs
> an admissible infinite support**. Finite checks are consistency and falsification evidence
> only."

Knowing the source matters: the bar is the corpus's own anti-recurrence guard, written after
25 families, not an arbitrary standard.

### 76.6 Two facts about the tree, recorded because they are easy to get wrong

`TwentyOneOneStepPropagation.lean` -- untracked and dirty in the Lean directory throughout
sections 74 and 75 -- is **not proof authority**. The closeout: *"The focused build on
2026-08-22 exits `1` with multiple proof errors, and the printed declarations contain
`sorryAx`. None of these attempted declarations is presently proof authority."* Anything read
out of that file is a proposal, not a theorem.

The closeout also carries a **non-authority notice**: it *"is not a current objective, work
queue, route selector, target selector, or priority surface"*, and *"no entry or working-memory
surface may inherit a next route from this document."* It records that family cluster 1--7 is
*"the main orthogonal positive route, with phase--scale coupling as the required new content"*
-- **I record that as a fact about the map and explicitly do NOT adopt it as my next route**,
because doing so is the exact inheritance the notice forbids.

**Status. NEGATIVE, and self-directed.** No mechanism opened, none eliminated. What changed:
the frontier question I had been asking for four iterations is malformed and is retired; the
best carry-free candidate in the corpus is proven to compute the carry; and my own section 66
is classified, for the first time, into a proof shape the corpus has already countermodelled.
Three of the last five iterations found the answer already on disk (T13/T29a now **fourteen of
seventeen**), and this time the thing on disk was a file whose title said exactly what it was.

## 77. The base-two filter -- a second, cheaper filter, and it rejects my own chain

Two sections of `SupportWordStructureLab.md` that I had never read (4g, 4d) plus one I read
only via its owner script (4b) change what I should be doing more than anything since the
socket criterion.

### 77.1 Section 4g: the conspiracy is the entire surviving population

By Bang's theorem, for `F` finite and `a in F` maximal for divisibility, a primitive prime
divisor `r` of `2^a - 1` survives into the reduced denominator, so `r | q`; for prime `q` this
forces `r = q` and `a = ord_q(2)`, whence `F` is a subset of `{1,2,3,6} union {d : d | ord_q(2)}`,
finitely enumerable. The count is then exact, not heuristic:

> **A non-Mersenne prime admits NO finite Mersenne sum at all, and a Mersenne prime `q = 2^e - 1`
> admits exactly two**, `F = {e}` giving `1/q` and `F = {1,e}` giving `1 + 1/q`.

The measure heuristic predicts `q` survivors among the `floor(qE)` lattice points `p/q`. So for
a non-Mersenne prime the required excess deaths equal `q` -- **the theorem demands that the
entire measure-predicted surviving population dies**. For `q = 10007`: predicted 10007, required 0.

### 77.2 The probe I was about to build has already been run, and it came back flat

I had selected an exhaustive per-`q` survivor census as this iteration's computation. The owner
script `required_excess_death_budget.py` says in its own docstring:

> "Section 4d/4b measured the deaths and found them matching the measure prediction **with no
> excess at all down to depth `2.5 x 10^4`**."

Section 4b's numbers: at `N = 2.5x10^4` over `q in {101,211,509,1021,4099,10007}`, 247 survivors,
148 deaths, **every death at rank <= 10** -- entirely inside the forced shallow regime -- and the
deepest death tracks `log_2(q/3)` to within one or two ranks across a factor of ten in `q`. Its
verdict: *"A death appreciably beyond `log_2(q/3)` would be the first arithmetic signal in this
problem; none has appeared."*

**So the conspiracy of 77.1 is completely invisible to depth 25,000.** Any mechanism must be
infinite-depth. That is a real constraint, and it retires the whole family of "measure the
survivors harder" probes -- including the one I had chosen this turn. **Fifteen of eighteen
iterations have now found the answer already on disk.**

### 77.3 Section 4d: the filter

With `z_n = (b^n - 1)^{-1}` and `T_n = sum_{k>n} z_k`, the gap series is

    gamma_n = z_n - T_n = sum_{j>=1} b^{-jn} (b^j - 2)/(b^j - 1),

**whose `j = 1` term vanishes if and only if `b = 2`.** At `b = 2` the gaps are `(2/3) 4^{-n}`,
*quadratically* smaller than the bridges `T_n ~ 2^{-n}`, and `|C_2| = 1`. For `b >= 3` the gaps
are `~ b^{-n}(b-2)/(b-1)`, the same order as the bridges, `|C_b| = 0`,
`dim_H C_b = log 2 / log b`. Measured on the certified forced greedy at depth 600: across
**2868 rational targets in bases 3, 4, 5, 7, 10, not one survives**, each base's deepest death
sitting at the predicted `log_2 q / log_2(b/2)`; base 2 has `415/669 = 0.6203 = 1/E` surviving.

Section 4d's operational consequence, which is the part I did not have:

> "**any proposed proof of Erdos 257 that would also go through for some `b >= 3` is thereby
> known to be insufficient**, because it would be proving something the gap structure already
> gives for free. A proof must use a property that fails the instant `b` exceeds 2."

**Read it precisely.** It disqualifies base-general arguments as *complete proofs of 257*; it
does not disqualify base-general *partial* theorems. The machine-checked reciprocal-summable
theorem is base-general and remains perfectly valid as a special case. The filter says such an
argument cannot be the whole thing.

### 77.4 Screening the filter before using it

Applied to three lanes whose verdicts were already known independently:

| lane | base-free? | filter says | independently known |
|---|---|---|---|
| divisor layer (T51, s5d) | yes -- divisor incidence has no base in it | insufficient | s5d: cannot obstruct |
| `Lambda` criterion (T55b, s5b) | yes -- exponent division works for any `b`, with `Z[1/b]` | insufficient | s5b: "not a new route" |
| reciprocal-summable theorem | yes | not a complete proof | true: it is a special case |

**Three for three.** The filter reproduces three verdicts that cost the corpus real work, which
is the screen I require of an instrument before reading its output.

### 77.5 Applying it to my own chain -- it fails

The corpus's own definition settles this without any derivation on my part. `CertificateKernel.lean`
states `supportCoeff` as the coefficient *"in which Erdos #257 is actually stated:*
`sum_{a in A} 1/(b^a - 1) = sum_n f_A(n)/b^n`*"* -- **written for general `b`, not for 2.**

Therefore the complement identity `f_A + f_{A^c} = tau`, the `F_2`-linearity
`Odd_A XOR Odd_E = Odd(d)`, the socket criterion `Odd_A = Sq XOR Odd_E`, and **both theorems I
machine-checked in section 75** hold verbatim at `b = 3`. They are base-free. By 77.3 they
cannot constitute a complete proof of Erdos 257.

**This is the second independent filter to reject section 66**, and it is much cheaper than the
first. T55c placed the socket in countermodelled shape (1) by an argument about syndeticity and
bounded windows. The base filter reaches the same verdict in one line, from the definition,
with no reference to the countermodels at all. **Two orthogonal filters, one verdict.** Section
66 is not retracted -- it is correct, and (P1)+(P1.5) are machine-checked -- but its ceiling is
now established twice over.

### 77.6 What the filter demands of any successor

The only structure that dies when `b` exceeds 2 is the vanishing of the `j = 1` gap term, i.e.
**gaps quadratically smaller than bridges** (`4^{-n}` against `2^{-n}`), equivalently
`|C_2| = 1` against `|C_b| = 0`. So a candidate route must consume the quadratic gap--bridge
separation somewhere essential. **That is a positive, checkable requirement**, and unlike the
five countermodelled shapes it tells me what a route must contain rather than only what it may
not.

### 77.7 A correction in section 4b I should hold against my own run lemmas

Section 4b withdraws its own earlier reading: *"There is no finite run length that implies
death."* The counterexample is decisive -- a support with `A cap [11,510]` empty has a run of 500
zeros and **survives trivially, because long runs place the orbit near a hole boundary and
always on the safe side of it.** Long runs are safe, not dangerous, which is the opposite of the
naive reading. I have four landed `socketRun_*` lemmas. I have **not** re-read them against this
correction and I am not claiming they are affected; I am recording that the check is owed.

**Status.** No new mathematics. What changed: one probe retired before it ran, because its answer
was already on disk and flat to depth `2.5x10^4`; one new and cheaper filter acquired, screened
3/3 against known verdicts; and **my own section 66 chain, including both machine-checked
theorems, shown base-free and therefore ceilinged for the second time by an independent route.**
One owed check recorded against my run lemmas.

## 78. The census is empty, the filter is two-sided, and my chain fails both axes

Section 77 left one forward-pointing question: **where does the corpus already consume the
quadratic gap-bridge separation**, the single property that distinguishes `b = 2`? Answered
this iteration, and the answer is nowhere.

### 78.1 The census: nothing uses it

Across the **164** markdown files of this directory (calibrators in the same runs: `Erdos` = 27
files, `bridge` = 19 files, `cylinder` = 10 hits in the file it was run against):

| probe | files | verdict |
|---|---|---|
| `gamma_n` / `\gamma_n` | 3 | `SupportWordStructureLab.md` (defines it), `CertificateSocketCollapse.md` (**mine, only since s77**), and `AnchorFourFiveBellmanPhaseNoGo.md` |
| `quadratic` | 12 | none about the gap-bridge relation |

**The third `gamma_n` file is a name collision, not a use.** `AnchorFourFiveBellmanPhaseNoGo.md`
line 46 defines `gamma_n = 2^n/(2^n - 1)` -- a Bellman recurrence coefficient, unrelated to the
gap series `z_n - T_n`. The `quadratic` hits elsewhere are LCM collision clocks escaping
quadratically (`OptimalCylinderRecutRenormalisation.md`) and the closeout's "superquadratically
separated dense bursts" (family 4) and "quadratic endpoint energy" (retired). None is the
gap-bridge separation.

**So: 25 mechanism families, 164 notes, and not one of them consumes the property that makes
`b = 2` different from every other base.** That is the census result, and it is exactly the
outcome section 77 flagged as possible. It does not name a route -- but it says the admissible
ingredient is *unused*, which is a very different situation from *tried and failed*.

### 78.2 Section 4e turns the filter two-sided

Section 4d varied the base. **Section 4e varies the constant**, and I had not read it. For
`z^{(c)}_n = 1/(2^n - c)`:

    z^{(c)}_n = 2^{-n} + c 4^{-n} + O(8^{-n}),   T^{(c)}_n = 2^{-n} + (c/3) 4^{-n} + O(8^{-n}),
    gamma^{(c)}_n = (2c/3) 4^{-n} + O(8^{-n}).

**The sign of the gap is the sign of `c`, and its scale is `4^{-n}` for every `c`.** The measured
table, exact rationals with a certified tail enclosure at depth 500:

| `c` | `z_n` | `sum z_n` | `lim 4^n gamma_n` | structure | analogue |
|---:|---|---:|---:|---|---|
| `-2` | `1/(2^n+2)` | `0.63225` | `-4/3` | full interval | **FALSE** |
| `-1` | `1/(2^n+1)` | `0.76450` | `-2/3` | full interval | **FALSE** |
| `0` | `2^{-n}` | `1` | `0` | full interval (`z_n = T_n` exactly) | **FALSE** |
| `+1` | `1/(2^n-1)` | `1.6066952` | `+2/3` | Cantor, `|C| = 1` | **OPEN -- Erdos 257** |
| `+2` | `1/(2^n-2)` | `0.8033476` | `+4/3` | Cantor | OPEN (`= E/2`, a rescaling of `c=1`) |

**The negative side is constructively false, with an explicit infinite witness.** At `c = -1`
every finite subsum of `1/(2^a+1)` has odd denominator while every value in `[0, 0.76450]` is a
subsum, so

    sum_{a in A} 1/(2^a + 1) = 1/2,   A = {1,3,5,6,7,9,13,15,17,18,19,21,22,26,...}

the forced greedy support, run to depth 2000 selecting 1025 ranks. **One step down the family,
the analogue of Erdos 257 is not merely easier -- it is false, and the counterexample is
written down.** Section 4e's conclusion:

> "**Erdos 257 occupies the unique parameter point at which the achievement set is a Cantor set
> of full measure.** Any argument that does not degrade as `c` decreases to `0` or `b` increases
> to `3` is proving something that is either false or free."

**So Filter 2 becomes two-sided**: a route must degrade in BOTH parameters, not one.

### 78.3 The corner, stated jointly

Putting 4d and 4e together in one expansion. For `z_n = 1/(b^n - c)` the gap is

  leading order `b^{-n} (b-2)/(b-1)`  -- **vanishes iff `b = 2`**;
  at `b = 2` the next order is `(2c/3) 4^{-n}`  -- **vanishes iff `c = 0`, negative iff `c < 0`**.

`(b,c) = (2,1)` is therefore a *corner*: the first-order term vanishes in the base direction, and
the surviving second-order coefficient is positive and minimal among the integer choices that
leave the analogue open. Both filters are one-sided readings of that single corner.

### 78.4 My chain fails the second axis too -- and this one I derived

Section 77 showed the s66 chain is base-free from the corpus's own definition. The `c` axis
needs one line of algebra. Expanding geometrically,

    1/(2^a - c) = sum_{j>=1} c^{j-1} 2^{-ja},

so for any support `A`,

    sum_{a in A} 1/(2^a - c) = sum_n 2^{-n} * ( sum_{a | n, a in A} c^{n/a - 1} ).

**The bracket is a `c`-weighted divisor incidence, and at `c = 1` it is exactly `supportCoeff`.**
Now the complement identity is a statement about weights only:

    sum_{a | n, a in A} w_a  +  sum_{a | n, a not in A} w_a  =  sum_{a | n} w_a

holds for **any** weight system `w`, hence for every `c`. So the complement identity -- and with
it the `F_2`-linearity built on it -- is `c`-free as well as base-free.

**That is a third independent ceiling on section 66, on the axis section 77 did not test.** T55c
placed it in countermodelled shape (1); T56a killed it on the base axis; this kills it on the
constant axis. **Section 66 is still not retracted -- the criterion is correct and (P1)+(P1.5)
are machine-checked -- but it now fails every filter the corpus possesses.**

### 78.5 Section 4e.1: even denominators need no infinitude argument

A fact I did not have, and it removes a side condition rather than adding one:

> Every finite subsum of `1/(2^a-1)` has odd denominator. Hence a target `x` with **even**
> denominator can never be a finite Mersenne sum, and so **if a target with even denominator
> survives the forced greedy, it is a counterexample outright -- the support is infinite
> automatically.**

The census already carries such targets: `q = 512, 1024, 2048, 4096` all show survivor fractions
`0.623`--`0.624`, and **`1013/2048` survives to certified depth `4 x 10^4`**. It also corrects
the target ring in the `Lambda` criterion: for even denominators the condition is
`Lambda(l,A) in Z[1/2]`, not `Z`.

**Read this against T56b before it looks like evidence.** A survivor fraction of `0.623` is
`1/E` -- exactly what the measure model predicts -- so surviving to `4 x 10^4` is not evidence of
a counterexample; it is what a generic point does. What 4e.1 supplies is the cleanest candidate
*shape*: for even `q`, survival alone would settle the problem, with no infinitude argument
attached.

**Status.** No new mathematics beyond one line of algebra in 78.4. What changed: the
quadratic-separation census came back **empty across 164 files and 25 families**; Filter 2 is now
**two-sided** with `c` as well as `b`, and section 4e supplies an explicit infinite-support
rational witness one step down the family; and my own section 66 chain is shown `c`-free,
**failing every filter the corpus has**. One candidate shape recorded (even denominators) with
its measure-model caveat attached so it cannot later be misread as evidence.

## 79. I tried to construct, and the construction died three ways -- one of which retires my own coordinate

Section 78 ended with a positive-sounding instruction: consume the quadratic gap-bridge
separation. I attempted it. The attempt produced three things, all negative, and the third is
the most consequential fact about my own programme that I have found.

### 79.1 The normalisation I derived is section 2's, up to a complement

Working in the remainder coordinate `u_n = r_n/T_n`, the death condition `T_n < r_n < z_n`
becomes `1 < u_n < 1 + h_n` with `h_n = gamma_n/T_n`, and the greedy is a doubling map with a
hole at `1`. At `b = 2`, `h_n ~ (2/3)2^{-n} -> 0` geometrically; at `b >= 3`, `h_n -> b-2`, a
CONSTANT. So the entire base filter is the single question *does the relative hole width
vanish*.

I checked before claiming it, and section 2 has it already: `psi_n = 1 - r_n/T_n` -- my `u_n`'s
complement -- with hole `H_n = (rho_n, 1-rho_n)`, `rho_n = T_n/T_{n-1}`, and

    |H_n| = gamma_n / T_{n-1} = (1/3) 2^{-n} (1 + O(2^{-n})).

Its own consequence 2 states the criticality I re-derived: *"The perturbation and the hole are
the same order, `2^{-n}`. That is the criticality of the exponent 2: with `z_n = 1/(B^n-1)`,
`B >= 3`, one gets `T_n/z_n -> 1/(B-1) < 1`, `|C| = 0`, and holes of order one. Base 2 is the
exact boundary case."* **Not novel. T51b paid again, and this time before I wrote the claim
rather than after.**

### 79.2 CORRECTION to section 78: I over-read the positive form of the filter

Section 78 said the filter's positive form is "a route must consume the quadratic separation
somewhere essential", and treated that as forward-pointing. **That reading is wrong, and
section 4d says why in its own voice**: *"For `b >= 3` the survivors carry measure zero,
rationals die at a computable depth, and a measure or gap-density argument has room to operate.
At `b = 2` the survivors carry full measure, so no argument of that shape can exist."*

The separation is what makes the hole NARROW, and a narrow hole is exactly what makes survivors
generic (`|C| = 1`). **So the separation is a fact in the counterexample's favour, not a lever
for the theorem.** "Must degrade as `b` increases to 3" therefore does not mean "must use
`gamma_n`"; it means **"must be an argument that measure cannot already supply"** -- because at
`b >= 3` measure supplies it for free.

That collapses most of the distance I claimed between the filters. F1's five countermodelled
shapes are all metric or local; F2/F3 demands non-metric. **They are plausibly the same demand
wearing two costumes**, which would make section 77's "two orthogonal filters, one verdict"
an overstatement about the filters even though its verdict on section 66 stands. I state this
as a hypothesis about the filters, not a theorem: the extensions may coincide, the tests do not.

### 79.3 The one bound I did derive is correct, base-general, and already family 2

Since the representation converges, `r_n = sum_{a in A, a >= n} z_a <= T_{n-1}`, and for an
infinite support `r_n > 0` with denominator dividing `D_n = q * lcm{2^a - 1 : a in A, a < n}`.
Hence `1/D_n <= r_n <= T_{n-1}`, so

    D_n >= 1/T_{n-1} ~ 2^{n-1},   i.e.   log_2 q + sum_{a in A, a < n} a  >=  n - 1.

With `k = |A cap [1,n)|` this forces `k >~ sqrt(2n)`: an infinite-support representation of
`p/q` needs at least about `sqrt(2n)` support elements below `n`. Correct, and not vacuous.

**And dead on both filters.** It uses `T` and never `gamma`, so it is base-general and fails
F2/F3. And it is precisely family 2 of the master map -- *"Rational-support carry and
denominator height: gives exact common-multiple lower bounds and unbounded carry, **but the LCM
scale can dwarf the Archimedean scale**"* -- which is exactly the failure mode here, since
`D_n ~ 2^{n^2/4}` for a positive-density support swamps the `2^{n-1}` it must beat. F1 shape (3),
"denominator height", with the countermodel already on file. The language appears in six notes
including `DenseSupportDichotomyAttack.md` (calibrator: `denominator` in 83 files).

### 79.4 THE FIND: the divisor sum is a coordinate artefact

Section 2, consequence 1, which I had never read:

> "**The intrinsic dynamics contains no divisor sum.** `f_A(n) = sum_{d | n} b_d` is an artefact
> of the integer-carry coordinate. In (2.2) the whole problem is a one-dimensional
> non-autonomous expanding map. **Divisor structure re-enters only through the *rationality of
> the initial point*.**"

`f_A` is the object my entire section 66 chain is built on, and the object both machine-checked
theorems of section 75 are about. **The intrinsic problem does not contain it.** It is not a
layer, not a mechanism, and not a coordinate the problem prefers -- it is what appears when you
choose the integer-carry coordinate, and it disappears when you do not.

This is a **fourth** ceiling on section 66, and unlike the first three it is not a
classification -- it is a statement that the object is not intrinsic. T55c said the socket is a
bounded-window argument; T56a said it is base-free; T57c said it is `c`-free; **this says the
thing it is an argument about is a coordinate artefact.** Section 66 remains correct and
(P1)+(P1.5) remain machine-checked; what changes is that the divisor coordinate is now the
weakest place to stand, not the natural one.

### 79.5 The sharpest statement of the difficulty, from section 3

The run law: with `delta_m = T_m - r_{m-1} >= 0` the survival margin at a skip, ranks
`m+1..m+L` are all selected and `m+L+1` is skipped, where `L = max{i >= 0 : T_{m+i} >= delta_m}`,
so `delta_m ~ 2^{-(m+L)}`; and **`x` is not in `C` if and only if the greedy word ends in an
infinite run of 1s.** Hence section 3's closing line, which is the quantitative shape of the
whole problem:

> "Death at rank `m` requires a run of length `~ m`. **The gap between what death requires and
> what the word supplies grows linearly while the word's own fluctuation grows
> logarithmically.**"

Linear demand against logarithmic supply. The conjecture asks the arithmetic to manufacture
runs exponentially longer than a generic word ever produces -- for every rational, forever.

**Status. NEGATIVE, and it was a construction attempt rather than a read.** The normalisation I
built is section 2's; the bound I derived is family 2's with its failure mode already named; and
my reading of section 78's positive form was wrong and is corrected here at source. The one
durable gain is section 2 consequence 1: **the divisor sum, on which my whole chain stands, is a
coordinate artefact of the integer-carry picture.** I did not find an argument that consumes the
separation, and section 4d's own text now suggests that phrasing was never the right target.

## 80. There is no signal. The corpus measured it, my lane was already worked, and I have been on the wrong side of the problem

I set out to ask what the rationality of `psi_0 = 1 - x/E` buys in the intrinsic map -- the one
entry point section 2 allows for divisor structure. I grepped first. Two files answer it, and
between them they end the lane and reorient the problem.

### 80.1 The lane was already worked, in a sharper form

`RunLengthMarginLawAndDivisorMultiplicity.md` section 16 has the exact Diophantine statement.
With `x := F(y)`, the support word read as a binary number, death at rank `n` is
`|{2^{n-1} x} - 1/2| < h_n` with `h_n ~ (1/6)2^{-n}`, which is exactly

> `y` survives forever **iff** `|x - a/2^n| >= (1/3) 4^{-n}` for every `n` and odd `a`.

**A dyadic Diophantine condition at exponent 2, with explicit constant `1/3`.** That is my
question answered in a better coordinate than the one I was going to use -- and the answer to
"does rationality help" is measured, not speculative:

*Sufficient condition.* If `x` is badly approximable with `sup a_i = K` then
`|x - p/q| > 1/((K+2)q^2)`, so the condition holds when `K <= 1`. **Only noble numbers qualify**
-- partial quotients eventually all `1`, Hurwitz constant `1/sqrt 5 = 0.447 > 1/3`. Section 16's
own words: *"The sufficient condition sits at the very edge of the Lagrange spectrum, which is
why no soft argument reaches it."*

*How far are the rationals?* `x = F(y)` to 900 bits, continued fraction ~520 terms:

| `y` | 1/2 | 1/21 | 4/9 | 1/465 | 1/5 | 5/12 | 2/21 |
|---|---|---|---|---|---|---|---|
| max `a_i` | 745 | 3394 | 2559 | 465 | 3782 | 4031 | 4386 |
| median `a_i` | 2 | 2 | 2 | 2 | 2 | 2 | 2 |

**Median 2, maxima in the thousands -- textbook Gauss-Kuzmin.** No rational is remotely close to
badly approximable. **T51b pays a seventeenth time in twenty.** I would have re-derived a worse
version of this.

### 80.2 The one-way result: there is no signal, and that is why 25 families died

`GapAvoidanceReductionAndEquidistribution.md` section 3, labelled **[COMPUTED -- the one-way
result]**. Normalise the skip position `v_n = rho_{n-1}/w_n in [0,1)`; fatal iff
`v_n > 1 - G_n/w_n`. Pooled over ~`2.9x10^5` skips at rank `>= 40`:

| `q` range | `P(v > 1-eps)/eps`, `eps = 2^-2 ... 2^-12` |
|---|---|
| `3..200` | `0.94 -> 0.79` (biased **away** from danger) |
| `1e5..2e5` | `1.00 -> 1.16` (flat) |
| `1e12..2e12` | `1.00 -> 1.01` (flat) |

The repulsion at small `q` is *"a small-denominator transient only"*. For large `q` the skip
position is **equidistributed to measured precision `2^-12`**, and the failure rate equals the
geometric gap width exactly. Then, verbatim:

> "There is no congruence, height, phase, density, ownership, window, or carry signal
> distinguishing safe from fatal orbits, **because there is no signal**. This is a structural
> explanation for why all ~25 mechanism families in this corpus died: **each was searching for a
> bias that the measurement says is absent.**"

**This is the fact under T55a's five countermodelled shapes and under T57b's empty census.** The
shapes are not five separate walls; they are five faces of one measurement. It also explains my
own four ceilings on section 66 without needing any of them.

### 80.3 The reformulation worth memorising

Section 1 of the same file, **[PROVED]**: survival iff the orbit never enters a gap, and the
gaps are explicit -- for each finite `F` with `max F = n`, the interval
`(sigma_F - G_n, sigma_F)` immediately below the finite Mersenne sum `sigma_F`, with
`G_n = w_n - Tail_n ~ (2/3)4^{-n}`. Hence:

> **Erdos 257 asserts that the finite Mersenne sums approximate every rational from above to
> within `G_{max F}`** -- an approximation `2^n` times sharper than the `2^{-n}` spacing of
> those sums predicts.

That single sentence says why the problem is hard better than anything else I have read: it
demands one-sided approximation quality far beyond what the counting of the approximating family
supplies. And the reduction *"reproduces the corpus's own greedy supports exactly... with no
divisor counts, no LCM, no carries, no Boolean ancestry"* -- independent confirmation of T58.

### 80.4 I have been on the wrong side of the problem

Section 2 measured 323,825 random `p/q`, `q` odd near `10^9`, at exact fixed point: **fatal
50.04%, alive at depth 64 = 49.96%**, with `P(fatal at n) = 0.25 G_n/w_n` to sampling noise --
*"the failure process is exactly Bernoulli with summable rate"*, deepest fatal rank 16.

Section 4 draws the consequence, and labels it **[HEURISTIC]**, which I keep attached:
*"Under the measured Bernoulli law a target alive at depth `R` survives forever with probability
`1 - O(2^{-R})`. **Counterexamples are therefore abundant (about half of all rationals), not
rare.**"* And: *"The binding difficulty is **certification, not discovery**: proving one orbit
avoids gaps forever is Diophantine avoidance where the residual denominator is `~2^{n^2/4}`
against a window of relative width `2^{-n}`. **No height argument can ever close that.**"*

**I have spent this entire session trying to prove Erdos 257 true.** The corpus's own measurement
says roughly half of all rationals appear to survive, and that the hard part is not finding a
counterexample but certifying one. The caveat stays attached (T56b/T57d): survival to depth `R`
is not survival, and the extrapolation is explicitly heuristic. But the orientation is wrong way
round, and no section of mine had noticed.

### 80.5 The one live frontier, stated by the corpus, and it is not any of the five shapes

`RunLengthMarginLawAndDivisorMultiplicity.md` section 10, after declaring the height route dead
(`rho_n` denominator `~2^{0.3n^2}` against a window `~(2/3)4^{-n}`), leaves exactly one object:

    0 <= tau_A(m) = eps_m + 2 C_{m-1} - C_m <= tau(m)   for every m,
    1_A = mu * tau_A   must be a 0/1 indicator with infinite support.

with three observations:

* **the carry recursion is local and contractive** -- `C_{m-1} = floor((tau_A(m)+C_m)/2)` run
  downward halves its error each step, so `C_m` is pinned to within `2^{-L}` by `tau_A` on a
  window of length `L` above `m`. **The carry structure is effectively a finite-state machine.**
* **the divisor structure is global** -- `tau_A(m)` reads every divisor of `m`, at every scale.
* **at a prime they meet**: `tau_A(p) = 1_A(1) + 1_A(p) <= 2`, while typical `tau_A(m) ~ (1/2)ln m`
  (`~4.5` at `m = 9000`). **The carry sequence is forced to dip hard at primes, and by Bertrand
  every dyadic block `(n, 2n]` contains one.**

> "The open question is whether a local finite-state carry automaton can be made compatible with
> a global divisor sum. **That interaction is not a height argument, not a congruence, and not a
> statistic, so nothing measured above rules it out.**"

**Note the fine distinction against F1 shape (5).** Shape (5) is countermodelled for arguments
that *use* an eventually periodic or finite-state carry rule as their mechanism. This route uses
finite-state-ness as a **constraint to be contradicted** by the global divisor sum. Those are
opposite uses of the same property, and the corpus says nothing measured rules this one out.

**Status. NEGATIVE for my lane, and a reorientation.** The Diophantine question I chose was
already answered in a sharper coordinate, with rationals measured Gauss-Kuzmin generic against a
sufficient condition that only noble numbers meet. The deeper find is that **there is no signal**
-- measured to `2^-12` -- which is the single fact beneath the five shapes, the empty census, and
every ceiling I have put on my own section 66. And the corpus's own numbers point the opposite
way from the direction I have been pushing. **Third read-heavy iteration in a row; it prevented a
re-derivation and produced a reorientation, but I have not produced mathematics in three turns
and I am saying so.**

## 81. I attacked the live frontier, my prediction was refuted, and the frontier's decisive question came back NEGATIVE

First iteration in four that ran computations rather than reading. Everything below is a
captured `rc = 0` from an instrument that already existed and that I had never executed.

### 81.1 The derivation was pre-instrumented -- and the corpus's version is tighter than mine

I derived, by hand: the downward carry telescopes to `C_{m-1} = sum_{k>=0} tau_A(m+k) 2^{-(k+1)}`;
the digit word is a parity, `eps_m = (tau_A(m) + C_m) mod 2`; and at a prime the divisor supply
collapses. Then I grepped. **Four scripts already implement exactly this**, and two of them
improve on what I had:

* `carry_closed_form.py` swaps the summation order to
  `C_m = floor( sum_{d in A} 2^(d - ((-m) mod d)) / (2^d - 1) )` -- **the Mersenne weights
  reappear as an ALMOST-PERIODIC sum**, each `d in A` contributing a term depending only on
  `m mod d`. Sharper than my form, with expectation `sum_{d in A, d<=m} 1/d ~ (1/2) ln m`.
* `carry_peaks_at_primes.py` has the prime dip **as a theorem, and tighter than mine**: since
  `1` is never in `A` (`w_1 = 1` exceeds every target below 1), `tau_A(p) = 1_A(p)` lies in
  `{0,1}` -- **not my `<= 2`**. Hence `2 C_{p-1} <= C_p + 1` at every prime, and dually the
  carry's global maximum should sit AT a prime: 9 of 9 targets, against prime density `0.111`.
* `carry_divisor_bound.py` supplies the reformulation I never reached:
  `0 <= C_m <= Theta(m) := sum_{k>=1} tau(m+k) 2^{-k}`, purely arithmetic, so
  **Erdos 257 iff the forward carry eventually forces `C_m` above `Theta(m)`.**
* `carry_window_automaton.py` measures the finite-state question directly.

**T51b pays an eighteenth time in twenty-one, and this time it corrected an error in my own
algebra** -- my prime bound was off by one because I forgot `1 not in A`.

### 81.2 My prediction was REFUTED by measurement

I predicted, before running: `C_m` unbounded (since `C <= sum 2^{-(k+1)} tau(m+k)` and `tau` is
unbounded), hence look-ahead `L ~ log log m` growing, hence **not** finite-state -- which would
have weakened the whole frontier. Falsifier stated in advance: a bounded `L` collapses the
objection.

`carry_window_automaton.py`, depth 6000, `m` in `[2000,3500)`:

| target | `L(m)` min / median / p90 / max | distinct carry values | `tau_A` at primes (mean, max) | `tau_A` elsewhere (mean) |
|---|---|---|---|---|
| 1/21 | 7 / 7 / 9 / 9 | 13 | 0.4917, **1** | 3.9891 |
| 4/9 | 7 / 7 / 10 / 10 | 14 | 0.5057, **1** | 4.6530 |
| 1/465 | 7 / 7 / 10 / 12 | 12 | 0.5070, **1** | 3.3075 |

and `carry_divisor_bound.py` at depth 8000 gives `max C = 15..17` for every target tested.
**The carry is bounded (`<= 17` over 8000 ranks, six targets) and the look-ahead is bounded
(7 to 12).** `log_2(17) ~ 4.1` plus overhead is exactly the measured `L ~ 7`, so the two
measurements agree with each other.

**My objection is refuted twice over. The automaton IS effectively finite-state at these
depths, and the corpus's framing was right.** My error was bounding `C` by `Theta` -- using
`tau_A <= tau` -- when the actual `tau_A` runs near `4` against `tau` near `ln m`. **Twenty-seventh
wrong prediction on record.** The prime bound `tau_A(p) <= 1` is confirmed: measured max is
exactly `1` on all four targets, mean `~0.5`.

### 81.3 The frontier's decisive question, answered NEGATIVE

`carry_divisor_bound.py` states the test itself: *"A ratio bounded away from 1 means the divisor
bound is slack and cannot be the binding constraint; a ratio approaching 1 infinitely often
means it is."* Depth 8000:

| `y` | max `C` | max `C/Theta` | at `m` | mean `C/Theta` | `#(ratio>0.9)` | `#(ratio>0.99)` |
|---|---:|---:|---:|---:|---:|---:|
| 1/2 | 17 | 0.74950 | 6341 | 0.43078 | **0** | **0** |
| 1/21 | 16 | 0.62390 | 7134 | 0.35434 | **0** | **0** |
| 4/9 | 17 | 0.68488 | 7534 | 0.39757 | **0** | **0** |
| 1/465 | 15 | 0.59073 | 2582 | 0.28491 | **0** | **0** |
| 1/5 | 16 | 0.69959 | 5548 | 0.34490 | **0** | **0** |
| 5/12 | 16 | 0.69831 | 2891 | 0.38920 | **0** | **0** |

**The bound is slack by a factor of 1.3 to 3.5, with ZERO excursions past `0.9` across six
targets and 8000 ranks.** Erdos 257 is equivalent to `C_m` eventually exceeding `Theta(m)`; the
measurement says the two are not close and are not approaching. **MEASURED-IN-RANGE, not
proven** -- the ratio could climb past depth 8000 -- but the frontier the corpus described as
"nothing measured rules it out" now has a measurement, and it is unfavourable.

### 81.4 An instrument defect, and an unexplained outlier -- reported, not interpreted

**Defect.** `carry_window_automaton.py` line 68 searches `for L in range(1, 40)` and line 76
assigns the sentinel `need[m] = 99` on failure, so the printed "`L ... max 99`" means *not found
below 40*, not a look-ahead of 99. Worse, the agreement line is

    ok = sum(1 for m in range(lo_m, hi_m)
             if need[m] < 99 and (lambda s: s)(0) == 0)

and `(lambda s: s)(0) == 0` is `0 == 0`, a tautology. **The reported "window value == true carry
for 1500/1500" is really "an `L < 40` was found for 1500/1500" -- the agreement itself is not
checked.** The `L` numbers stand; the agreement column does not mean what it says.

**Outlier.** `y = 1/2` needs `L >= 40` at **every** `m` in the range, while 1/21, 4/9 and 1/465
need at most 12. Its other statistics are unremarkable (`tau_A` at primes mean `0.4700` max `1`;
elsewhere mean `4.3299`), and its carry is only marginally the largest (`max C = 17`, tied with
4/9), **so carry magnitude does not explain it.** `1/2` has an even denominator, hence by section
4e.1 can never be a finite Mersenne sum, and its digit word terminates rather than being purely
periodic -- but **I have not established that this is the cause, and I am not claiming it.**
Recorded as an open anomaly with its cause undetermined.

**Status. A real attempt, with computation, and three results.** My prediction was refuted and
the automaton is finite-state as the corpus said. **The frontier's own decisive test came back
negative in range: the divisor bound is slack, zero excursions above `0.9`.** And the instrument
that measures the finite-state question contains a tautological no-op in its agreement check,
plus one target it cannot resolve at all. No one-way result; the lane is narrowed, not closed.

## 82. The `1/2` anomaly is SETTLED, and it was the seed -- plus a correction to my own s81

Section 81 recorded `y = 1/2` needing look-ahead `L >= 40` at every `m` while 1/21, 4/9 and
1/465 needed at most 12, with cause explicitly undetermined. It is now determined, it is
instrumental, and the same defect was in the probe I wrote to test it.

### 82.1 First, a correction to s81 (T60c)

I claimed the printed agreement column of `carry_window_automaton.py` was meaningless because
the line above it computes `ok` using `(lambda s: s)(0) == 0`, a tautology. **That was wrong.**
The tautological `ok` is computed and **never printed**; the printed line uses `exact`, which
does compare the window value against the true carry `C[m]` and is a real check. **The
agreement column means what it says.** The tautology is dead code -- a genuine defect, but a
harmless one. The `L`-cap and sentinel criticisms in T60c stand unchanged. Corrected at source
in T60c and T61b.

### 82.2 The honest quantity, and the clean split

Bisimulating seeds `0` and `BIG = 64` under `C <- (tau_A + C)//2` halves their difference each
step, so that instrument's `L ~ 7` is `log_2(64)` -- **the seed range, not the carry.** The
quantity actually wanted is

    Lstar(m) = min { L : descending from seed s at m+L reproduces C[m] exactly },

with `C[m] = floor(2^m p/q) - sum_{j<=m} tau_A(j) 2^{m-j}` computed exactly in integers. My
probe `scripts/carry_lookahead_parity_probe.py` measures it, over seven power-of-two
denominators against six odd controls, cap `200`, depth 6000, 800 ranks each. Predictions and
falsifier were written into the docstring before the run.

**Seeded from below (`s = 0`), the split is perfect:**

| cohort | targets | `Lstar` med / max | unresolved |
|---|---|---|---|
| even `q` (2, 4, 8, 512, 1024, 2048, 4096) | 7 of 7 | -- | **800/800** |
| odd `q` (21, 9, 465, 5) | 4 of 4 | 3-4 / 6-12 | **0/800** |

(`1/3` and `1/7` are absent by construction: they equal `w_2` and `w_3` exactly, are finite
Mersenne sums, and terminate rather than running.) The stated falsifier -- one even `q` resolving
small, or one odd `q` failing -- did not fire.

### 82.3 But the mechanism is the SEED DIRECTION, and the second run proves it

From `eps_j = (tau_A(j) + C_j) mod 2`: a power-of-two denominator has a terminating expansion,
so `eps_j = 0` and **`tau_A(j) + C_j` is EVEN for every large `j`.** Under `a <- (tau_A + a)//2`:

* seed one **above** truth: `tau + C + 1` is odd, floor gives `(tau+C)/2` -- **merges**;
* seed one **below** truth: `tau + C - 1` is odd, floor gives `(tau+C)/2 - 1` -- **persists**.

So a from-below seed can never close a deficit against a terminating-`eps` target. Re-running
with a from-above seed `BIGSEED = 4 max C + 8`:

| cohort | `Lstar_up` med / max | unresolved from above |
|---|---|---|
| even `q`, all seven | **6-7 / 6-7** | **0/800** |
| odd `q`, all four | **7-8 / 9-10** | **0/800** |

**Every target resolves from above, with `L <= 10`.** The even-`q` targets are in fact *tighter*
than the odd controls. **The anomaly is entirely an artefact of seeding from below**, and my
predicted mechanism is confirmed by the flip.

### 82.4 What this does and does not establish

**Establishes.** The carry is a bounded-window function of `tau_A` for **every** target tested,
even and odd denominators alike, with `Lstar <= 10` from above. That **strengthens T60a** -- the
automaton is finite-state -- and extends it to the even-denominator class that T57d singles out
as the counterexample-outright shape. It also shows **both** instruments, the corpus's and my
own first version, were measuring seed-direction sensitivity rather than determinacy; the
correct measurement seeds from above, or brackets with both.

**Does not establish.** Nothing about Erdos 257. The even/odd difference that looked like the
first target-specific structural signal of this session is not a signal at all -- consistent
with T59, which says there is none. The measure-model caveat stays attached: `1013/2048`
surviving to certified depth `4x10^4` is what a generic point does, since `0.623 = 1/E` is
exactly the measure prediction.

**Status. The capture is DISCHARGED and the answer is negative-instrumental.** One anomaly
explained, one of my own s81 claims retracted, one instrument written that measures the right
quantity. **A prediction I wrote in advance was confirmed for once** -- the seed-direction
mechanism -- against twenty-seven refuted ones on record. No progress on the problem.

## 83. T60 STRENGTHENED at depth 30000, the prime bound saturates 8 of 9, and one instrument is too slow to run

Prediction written before the run: the ratio stays bounded below `0.9` and `max C/Theta` creeps
only logarithmically. Falsifier stated in advance: any single excursion above `0.9`, or a max
growing steadily with depth, flips T60 from "slack" to "possibly binding".

### 83.1 The depth extension -- prediction CONFIRMED

`carry_divisor_bound.py`, captured `rc = 0`, depth `8000 -> 30000`, a `3.75x` increase:

| `y` | `max C` 8000 -> 30000 | `max C/Theta` 8000 -> 30000 | at `m` | `mean C/Theta` | `#(>0.9)` |
|---|---:|---:|---:|---:|---:|
| 1/2 | 17 -> 23 | 0.74950 -> **0.74950** | 6341 -> **6341** | 0.4308 -> 0.4392 | **0** |
| 1/21 | 16 -> 24 | 0.62390 -> 0.66131 | 7134 -> 13879 | 0.3543 -> 0.3701 | **0** |
| 4/9 | 17 -> 24 | 0.68488 -> 0.73437 | 7534 -> 18671 | 0.3976 -> 0.4101 | **0** |
| 1/465 | 15 -> 24 | 0.59073 -> 0.61826 | 2582 -> 15180 | 0.2849 -> 0.3089 | **0** |
| 1/5 | 16 -> 24 | 0.69959 -> 0.71021 | 5548 -> 22864 | 0.3449 -> 0.3625 | **0** |
| 5/12 | 16 -> 24 | 0.69831 -> 0.71367 | 2891 -> 29163 | 0.3892 -> 0.4003 | **0** |

**Still zero excursions above `0.9`, and none above `0.99`, at four times the depth.** The maxima
move by `+0.010` to `+0.049`, and `1/2`'s record is **bit-identical** at the same rank `m = 6341`
-- 22,000 further ranks failed to beat a record set below 8000. Note `max C` itself grew from
`15-17` to `23-24` while the ratio held: `Theta` grows with `C`, which is exactly why the ratio
is the right statistic and the raw carry is not.

**T60 is strengthened.** The divisor bound `0 <= C_m <= Theta(m)` is slack by `1.35x` to `1.6x`
at the tightest point of six targets across 30000 ranks, and the frontier's own criterion --
*"a ratio approaching 1 infinitely often means it is [binding]"* -- is not met. **Still
MEASURED-IN-RANGE: 30000 is not infinity, and the slow upward creep is real if tiny.** But the
in-range verdict now rests on four times the evidence. **Second prediction confirmed in two
iterations, against twenty-seven refuted.**

### 83.2 The prime bound saturates, and the carry's maximum sits at a prime 9 times out of 9

`carry_peaks_at_primes.py`, captured `rc = 0`, depth 8000, first execution:

| `y` | `max C` | `max C_(p-1)` | `floor((maxC+1)/2)` | saturated | `argmax C` at a prime | `mean C` | `mean C_(p-1)` |
|---|---:|---:|---:|---|---:|---:|---:|
| 1/2 | 17 | 9 | 9 | **yes** | 1.000 | 3.969 | 2.837 |
| 1/21 | 16 | 8 | 8 | **yes** | 1.000 | 3.345 | 2.167 |
| 4/9 | 17 | 9 | 9 | **yes** | 1.000 | 3.757 | 2.701 |
| **1/465** | 15 | **7** | **8** | **NO -- one short** | 1.000 | 2.732 | 1.764 |
| 1/5 | 16 | 8 | 8 | **yes** | 1.000 | 3.248 | 2.151 |
| 5/12 | 16 | 8 | 8 | **yes** | 1.000 | 3.709 | 2.310 |
| 3/7 | 16 | 8 | 8 | **yes** | 1.000 | 3.644 | 2.368 |
| 2/21 | 16 | 8 | 8 | **yes** | 1.000 | 3.478 | 2.368 |
| 3/8 | 17 | 9 | 9 | **yes** | 1.000 | 3.981 | 2.792 |

(`7/15` dies and is excluded.) The inequality `2C_{p-1} <= C_p + 1` is a theorem (T60b, from
`1 not in A`); **its saturation is empirical and holds for 8 of 9.** And
**`argmax C` lands on a prime for all nine targets**, against a prime density of
`1/ln 8000 = 0.111`. The instrument's own reading: *"the carry is large exactly where `tau_A(m)`
is small."* The mean carry at primes (`1.76-2.84`) runs consistently below the global mean
(`2.73-3.98`), as the halving bound requires.

**This is the sharpest local structure in the system**, and it is a confirmation of the corpus's
own derivation rather than anything new. It is not a signal separating safe from fatal orbits --
T59 stands.

### 83.3 An instrument I could not run, and a correction to my own brief

`carry_closed_form.py` -- which holds the almost-periodic form
`C_m = floor(sum_{d in A} 2^{d - ((-m) mod d)}/(2^d - 1))` **and the prime-slack distribution
`s(p) = (C_p + 1) div 2 - C_{p-1}` together with its vanishing set** -- **did not complete.**
Two attempts, both terminated by my own cap: `D = 8000` at 10 minutes, `D = 1500` at 7 minutes,
`rc = 143` (SIGTERM) both times, which is my timeout and not a fault in the script. Its own
default is `D = 3000`; it uses exact `Fraction` arithmetic over the whole support at every rank,
so the cost is real. **The slack distribution and its vanishing set remain UNMEASURED**, and a
prime where `s(p) = 0` -- where the halving bound is exactly tight and the carry pinned -- is
still the sharpest unexamined local constraint.

**Correction.** My own brief attributed the slack distribution to `carry_peaks_at_primes.py`. It
does not compute it: that instrument reports maxima and argmax only. The distribution belongs to
`carry_closed_form.py`. Mis-attribution recorded so the next attempt targets the right file with
a smaller `D` or a float path.

**Status. Two confirmations and one blocked measurement.** T60 survives a four-fold depth
increase with its margin intact, so the divisor bound is slack on the evidence available. The
prime halving bound saturates 8 of 9 and the carry's maximum sits at a prime 9 of 9 -- the
corpus's derivation confirmed by first execution. **No progress on Erdos 257**: everything here
describes the constraint system's shape, and T59 already says that shape carries no signal
separating survivors from deaths.

## 84. The prime slack is TWO-VALUED with a closed form -- derived, then confirmed on 20,358 primes

Section 83 left the prime-slack distribution `s(p) = (C_p + 1) div 2 - C_{p-1}` and its vanishing
set unmeasured, because the instrument holding it uses exact `Fraction` arithmetic and would not
finish. The quantity needs only `C_p` and `C_{p-1}`, both available from the fast integer
recurrence, so I reimplemented it -- and the algebra settled it before the computation ran.

### 84.1 The derivation

`tau_A(m) = eps_m + 2 C_{m-1} - C_m`, and at a prime the only divisor of `p` that can lie in `A`
is `p` itself, since `1` is never in `A` (`w_1 = 1` exceeds every target below 1). So
`tau_A(p) = 1_A(p)` in `{0,1}` and

    2 C_{p-1} = tau_A(p) - eps_p + C_p.                                   (*)

The left side is even, so **`tau_A(p) - eps_p = C_p` mod 2**, i.e. `C_p = 1_A(p) + eps_p` mod 2.
Splitting on the parity of `C_p`:

* `C_p` **even** forces `tau_A(p) = eps_p`, and then `s(p) = (eps_p - tau_A(p))/2 = 0`;
* `C_p` **odd** forces `tau_A(p) != eps_p`, and then `s(p) = (1 + eps_p - tau_A(p))/2`, which is
  `0` when `tau_A(p) = 1` and `1` when `tau_A(p) = 0`.

> **THEOREM.** `s(p) in {0,1}` for every prime, and `s(p) = 1` iff `C_p` is odd and `p` is not in
> `A`. Combining with `C_p = 1_A(p) + eps_p` mod 2 this collapses further:
>
>     s(p) = 1   <==>   p is NOT in A   AND   eps_p = 1.

**So the "distribution of the slack and where it vanishes" is a two-valued statistic with a
closed characterisation.** No amount of exact-rational computation was ever going to find
structure in it, which is why section 83's blocked instrument was blocked on the wrong question.

### 84.2 The check -- zero exceptions

`scripts/prime_slack_vanishing_probe.py` (mine), depth 20000, captured `rc = 0`, predictions and
falsifier written into the docstring before the run. Nine targets, **2262 primes each, 20,358
primes in total**:

| target | `s`-values | outside `{0,1}` | mismatch vs the characterisation | density(`s=1`) |
|---|---|---:|---:|---:|
| 1/2 | `{0: 2262}` | 0 | 0 | **0.0000** |
| 4/9 | `{0: 2261, 1: 1}` | 0 | 0 | 0.0004 |
| 1013/2048 | `{0: 2260, 1: 2}` | 0 | 0 | 0.0009 |
| 1/5 | `{0: 1722, 1: 540}` | 0 | 0 | 0.2387 |
| 1/465 | `{0: 1704, 1: 558}` | 0 | 0 | 0.2467 |
| 1/21 | `{0: 1699, 1: 563}` | 0 | 0 | 0.2489 |
| 2/21 | `{0: 1698, 1: 564}` | 0 | 0 | 0.2493 |
| 3/7 | `{0: 1697, 1: 565}` | 0 | 0 | 0.2498 |
| 5/12 | `{0: 1099, 1: 1163}` | 0 | 0 | **0.5141** |

**`TOTAL outside {0,1} = 0`, `TOTAL mismatch = 0`.** The probe also re-derives `tau_A(p)` from the
support independently and checks it equals `1_A(p)`; that check passed everywhere too, so the
premise of the theorem is verified rather than assumed.

### 84.3 The three density clusters are explained by the digit word's residues, not by survival

My prediction P3 -- density `~0.25` if parity and membership were independent -- holds for five
targets and **fails for four**, which is stated as a partial refutation. The closed form explains
all of it. Since `s(p) = 1` iff `p not in A` and `eps_p = 1`, and `eps` is eventually periodic
with period `l = ord_q(2)`:

* **`1/2`: `eps_m = 0` for all `m >= 2`, so `s(p) = 0` identically.** Density `0.0000` is a
  theorem, not a measurement -- the same terminating-`eps` structure that produced T61.
* **`1013/2048`** (`q = 2^11`, terminating): density `0.0009`, its two exceptions being primes
  inside the preperiod `m <= 11`.
* **`4/9`**: `l = ord_9(2) = 6`, and every prime above 3 is `1` or `5` mod 6, so `eps_p` samples
  only those two residues; `eps` vanishes there, leaving one exception at a small prime.
* **`5/12`**: `l = ord_3(2) = 2`, so **every odd prime samples the single residue `1` mod 2**; with
  `eps = 1` there, the density becomes `P(p not in A) ~ 1/2`. Measured `0.5141`.

**General form: density(`s = 1`) = P(`p not in A`) x (fraction of the residues mod `l` reachable
by primes on which `eps = 1`).** Primes cannot hit residues sharing a factor with `l`, so the
smaller `l` is, the coarser the sampling and the more extreme the density.

### 84.4 What this is and is not

**It is** a closed-form identity for the sharpest local constraint in the carry system, derived
and then confirmed with zero exceptions on twenty thousand primes, plus an explanation of its
target-to-target variation in terms of `ord_q(2)` and the digit word.

**It is not a signal.** `s(p)` is a function of `1_A(p)` and `eps_p` alone -- both already known
at `p` -- so it carries no information about survival that the support word does not already
carry. T59 stands: the variation tracks the residue structure of `eps` mod `ord_q(2)`, not
anything separating survivors from deaths. The vanishing set `{p : s(p) = 0}` is
`{p in A} union {p : eps_p = 0}`, which is explicit and structureless in exactly the way T59
predicts.

**Status. A theorem with a captured check, and no progress on Erdos 257.** The blocked
measurement of section 83 is discharged, and it turned out not to need measuring at all. Fourth
prediction confirmed (`s in {0,1}`, and the characterisation, both exactly); **P3's density
guess REFUTED for four of nine targets** and replaced by a derived formula.

## 85. The `Lambda` criterion, executed at last -- confirmed on five new targets, and one target I chose badly

Eleven iterations of intending to run `lambda_integrality_criterion_lab.py`. It ran this turn,
captured `rc = 0`, and the honest summary is: the criterion holds everywhere it was checked, the
numbers are at the truncation floor, and nothing separates survivors from anything.

### 85.1 Why new targets were required

Reading the interface first (`--targets --ranks --ells --bits --pad --write`), its default target
list is `1/21,4/9,1/5,2/21,3/11,90/511,17/29,1/465` -- **exactly the table already printed in
section 5b.** Re-running the defaults would have reproduced a known receipt and learned nothing,
so I ran genuinely uncovered denominators, keeping `1/21` as a calibrator: if the covered target
fails to reproduce integrality, nothing else in the run is believable.

### 85.2 The run

`--ranks 4000 --ells 800 --bits 256`, receipt
`state/.../lambda_new_targets_receipt.json`, `sha256=c4effe42850fecc6`:

| target | `ell_0 = ord_q(2)` | multiples checked | support size | max distance to `Z` |
|---|---:|---:|---:|---|
| **`1/21` (calibrator)** | 6 | 133 | 2026 | `2.53e-75` |
| `3/7` | 3 | **266** | 2004 | `2.53e-75` |
| `5/31` | 5 | 160 | 1977 | `2.58e-75` |
| **`1/127`** | 7 | 114 | **0** | **`0.0` exactly** |
| `1/13` | 12 | 66 | 1969 | `2.36e-75` |
| `1/23` | 11 | 72 | 2051 | `2.48e-75` |
| `1/47` | 23 | 34 | 1964 | `2.42e-75` |

**The calibrator reproduced**, and every target's `Lambda(k*ell_0, A)` is an integer to
`~2.4-2.6 x 10^-75`. That figure is **uniform across targets, which identifies it as the
truncation floor at 256 bits, not a measurement.** The earlier receipt's `1.7 x 10^-113` is the
same statement at higher precision -- consistent, not in tension. The count of multiples checked
is just `floor(800 / ell_0)`, so small-`ell_0` targets get the most checks: `3/7` with `ell_0 = 3`
got 266.

### 85.3 The target I chose badly

**`1/127` is not a test.** `127 = 2^7 - 1`, so `1/127 = 1/(2^7-1) = w_7` is a **single Mersenne
term**: the greedy takes rank 7 and terminates. The receipt says so exactly --
`greedy_stop_rank: 7`, `support_size: 0`, `head_sum_2^-j: 0.0`, empty `j_histogram`,
`max_distance_to_integer: 0.0`, and `monotone: true` alone among the seven. **I picked a
Mersenne-prime denominator for its small `ord_q(2)` without noticing that `1/(2^e-1)` is
literally a coin.** Recorded as a target-selection error.

What it does supply is a cross-instrument confirmation: section 4g classifies the finite Mersenne
sums of a Mersenne prime `q = 2^e - 1` as exactly `F = {e}` and `F = {1,e}`, and the carry-free
`Lambda` route independently lands on the `F = {7}` witness with `Lambda == 0`. Two different
coordinates, same classification.

### 85.4 The integer values, and what is not there

`Lambda(k*ell_0, A)` is an integer, and the receipt records *which* integer. For `1/21`, `3/7`,
`5/31`, `1/13` it is `0` across the sampled progression; `1/23` reaches `1` by `ell = 33`; `1/47`
reaches `2` by `ell = 782`. The instrument compares growth against `half_log_ell` (`2.6-3.3` over
these targets) and reports `monotone: false` for five of seven. So the integer creeps upward,
slowly and non-monotonically, at roughly the scale the instrument anticipated.

**No signal.** Every quantity here is a function of the support word and `ell` alone, and the
distances are all at the arithmetic floor. T59 stands: the carry-free coordinate confirms what
the carry coordinate said, which is exactly what T55b predicted when it showed
`Lambda(k*ell_0, A) = Qtilde_{k*ell_0}` -- *"literally the same number"*.

**Status. Confirmation, one self-inflicted error, no progress on Erdos 257.** The last unrun
instrument is now run; the criterion holds on five genuinely new non-trivial targets; the
uniform `~10^-75` is truncation, not evidence. **Fifth prediction confirmed** (integrality on all
new targets); **one wrong target choice recorded** (`1/127` is a coin).

## 86. The owed re-read: my four Lean lemmas are UNAFFECTED, because `socketRun` is a different object

Outstanding since section 77. The worry was that my landed lemmas might encode the reading
section 4b withdrew -- *"There is no finite run length that implies death"* -- since a support
with `A cap [11,510]` empty has a run of 500 zeros and **survives trivially**, long runs placing
the orbit near a hole boundary on the safe side. Read the source; the worry was misplaced, and
for a reason worth recording.

### 86.1 Two different runs

**Section 4b's run is the greedy word's**: consecutive *selected ranks*, with `R_N` the longest
such run below `N`. **`socketRun` is Erdos's 1948 object**: a run of `K` binary *zeros* in
`sum_n c(n)/2^n`, produced by forcing `2^k | c(N+k)` for `k = 1..K`, so that each of the first
`K` terms of the shifted sum is an integer. **Different coordinate, different object, no
overlap.** The retraction applies to greedy runs and says nothing about divisibility runs.

### 86.2 The four statements carry no dynamical content

All are elementary, and all live in `ReciprocalSupportIrrationality.lean`:

* `socketRun_excludes_odd_coeff` (`:1420`) -- from `2^i | c(N+i)` on the window plus
  `not (2 | c(N+k))`, derive `False`. One line: `2 | 2^k` for `k >= 1`.
* `no_socketRun_of_odd_in_window` (`:1439`) -- the contrapositive: an odd coefficient anywhere in
  a window of `g` forbids a run of length `g` starting at `N`.
* `socketRun_forces_pow_le_coeff` (`:1452`) -- `2^k | c(N+k)` and `c(N+k) > 0` give
  `2^k <= c(N+k)`, by `Nat.le_of_dvd`. Zero coefficients are exempt, since zero is divisible by
  everything.
* `no_two_powers_two_apart` (`:1487`) -- `2^w = 2^v + 2` with `v,w >= 2` is impossible, because
  `4` divides both powers while `2^v + 2` is `2` mod `4`.

**None of them says a run of any length implies death.** They say a divisibility run cannot
contain an odd coefficient, and that the coefficients inside one are exponentially large.

### 86.3 The file already states the caveat, in the right place

A fifth lemma of the family I had not listed, `socketRun_forces_pow_le_of_le`, carries this in
its own docstring:

> "**This is NOT a cap.** Since `c = tau_A` is unbounded for every infinite `A`, the right side
> grows without bound and no `K` is ever excluded outright. What the bound gives is a DEPTH: to
> observe a run of length `K` one must search out to where `c` reaches `2^K`. That is the
> quantitative form of *finite search never refutes existence* -- contrast the parity
> obstruction, which bounds the run for ALL `N` at once."

That is precisely the distinction T56c is about -- a depth is not a kill -- written where a reader
of the lemma will meet it. And `no_socketRun_of_odd_in_window`'s docstring runs the `A = N`
check unprompted: *"At `c = tau_N = d` the odd set is exactly the perfect squares, whose gaps
grow like `2 sqrt m`; the obstruction is vacuous there, as it must be, since Erdos carried the
construction out."* T25 satisfied inside the source.

### 86.4 One thing to keep straight about the syndeticity line

Line 1433 of the same docstring says *"arbitrarily long socket runs require `Odd_c` to have
unbounded gaps -- if `Odd_c` is syndetic the mechanism is unavailable, not merely unproven."*
That is the syndeticity claim T55c classified as countermodelled shape (1), and it is worth being
exact about what it does and does not assert: **it says Erdos's socket-run MECHANISM is
unavailable, not that Erdos 257 is settled.** So scoped, it is correct and the lemma supports it.
T55c's ceiling stands on the separate question of whether the socket criterion can be a complete
proof; the docstring never claims that.

**Status. Debt paid, verdict clean, capture retired.** Four -- in fact five -- lemmas re-read
against T56c and **unaffected**: `socketRun` is a divisibility object, section 4b's run is a
dynamical one. No self-caught error. The file's own docstrings already contain both the "NOT a
cap" caveat and the `A = N` sanity check, which is more discipline than I had credited them with.
**No progress on Erdos 257**; this closes an audit obligation, nothing more.

## 87. The s84 theorem is WRITTEN but UNPROVEN -- lease held; and the divisor bound at depth 100000

Two things this iteration: a Lean attempt that the project-build lease refused, and the depth
extension that was the sanctioned disjoint work.

### 87.1 The Lean file, and why it is not a claim

Section 84's theorem is pure integer parity, so it states abstractly with no divisor theory in
it. With `t = tau_A(p)`, `e = eps_p`, `cp = C_p`, `cm = C_{p-1}`, the carry identity in
natural-subtraction-free form is `t + cp = e + 2*cm`, and four theorems follow:

```lean
theorem primeSlack_halving   (ht : t <= 1) (he : e <= 1) (hcar : t + cp = e + 2*cm) :
    2 * cm <= cp + 1
theorem primeSlack_two_valued ... : (cp + 1) / 2 = cm  or  (cp + 1) / 2 = cm + 1
theorem primeSlack_eq_one_iff ... : (cp + 1) / 2 = cm + 1  <->  (t = 0 and e = 1)
theorem primeSlack_eq_zero_iff ... : (cp + 1) / 2 = cm  <->  (t = 1 or e = 0)
```

each closed by `omega`, which decides exactly this fragment -- linear naturals with division by
the literal `2`. Navigation receipt obtained (`recorded_exact_active_claim_match`), file written
at 2870 bytes.

**The build returned `rc = 75`.** Not a failure: the guard's own payload says
`status: validation_capacity_deferred`, `proof_scope: not_proof_evidence`,
`turn_action: finish_ready_disjoint_work_then_end_turn`, with `retry_loop` among its
`forbidden_actions`. The lease is genuinely held -- `pgrep` shows another owner's singleflight
(`--owner-surface erdos257-reset-sqrt-escape`, `--resource-class lean_build`,
`--capacity-wait-seconds 21600`) running a whole-library `Erdos257PeriodNoncollapse` build with
`lake build` children on `DiagonalPincerPrimeCertificates` modules.

Re-entry handles: ticket **`rct_51cbac976b5c5ef58f60`**, run
**`cmdrun_20260823T062239Z_42830_50f131ce423c`**, conflict key
`lean-project-build:formal_math/erdos257_period_noncollapse`, patch saved to the session
scratchpad as `PrimeSlackTwoValued.lean.patch` (2870 B) with the project file removed per T26a.

**The four theorems are UNPROVEN and UNCLAIMED.** Section 84's result stands on its derivation
and its 20,358-prime check, not on Lean.

### 87.2 The divisor bound at depth 100000 -- and a trend read carefully

`carry_divisor_bound.py` at `100000`, captured `rc = 0`, twelve and a half times the original
8000:

| `y` | `max C/Theta` at 8000 -> 30000 -> 100000 | increments | at `m` | `#(>0.9)` |
|---|---|---|---:|---:|
| 4/9 | `0.68488 -> 0.73437 -> 0.78916` | `+0.049, +0.055` | 93359 | **0** |
| 1/21 | `0.62390 -> 0.66131 -> 0.67800` | `+0.037, +0.017` | 71070 | **0** |
| 1/465 | `0.59073 -> 0.61826 -> 0.63698` | `+0.028, +0.019` | 99483 | **0** |
| 5/12 | `0.69831 -> 0.71367 -> 0.72287` | `+0.015, +0.009` | 85611 | **0** |
| 1/5 | `0.69959 -> 0.71021 -> 0.71021` | `+0.011, 0.000` | **22864 unchanged** | **0** |
| 1/2 | `0.74950 -> 0.74950 -> 0.75459` | `0.000, +0.005` | 38657 | **0** |

**Zero excursions above `0.9` at any of the three depths, and none above `0.99`.** `max C`
itself grew `15-17 -> 23-24 -> 33-35`.

**Read the increments, not the endpoints.** Four of six targets **decelerate**; `1/5` has
**stalled outright**, its maximum bit-identical at `0.71021` and at the same rank `m = 22864`
across 77,000 further ranks; `1/2` is nearly flat; and **only `4/9` accelerates**, `+0.049` then
`+0.055`. One of six behaving that way is comfortably inside what a maximum statistic does by
chance over more samples.

**So the honest verdict is that the data supports NEITHER extrapolation.** T62's in-range
finding stands and is now measured over a 12.5x span. But "slack forever" is not established,
and "approaching 1" is not established either -- and I should not have implied in section 83
that the creep was safely logarithmic, since across three depths the per-step increments are
mixed rather than uniformly shrinking. Corrected here.

**Status. One theorem written and NOT proven; one depth extension with a carefully-read
non-trend.** The Lean lane is blocked by a live foreign lease with a durable ticket for
re-entry; the divisor bound remains slack across 100000 ranks with no excursion, and the
direction of its slow drift is undetermined on six targets. **No progress on Erdos 257.**

## 88. RETRACTION: section 82 was a re-derivation. The mechanism was on disk seventeen hours earlier

The Lean lease was still held this iteration, so I took the sanctioned disjoint work and read
`RunLengthMarginLawAndDivisorMultiplicity.md` section 11, unread since section 80. It contains
my section 82 result.

### 88.1 The retraction, with the timing

Section 11's **Dyadic degeneracy** paragraph:

> For dyadic `y`, `eps_m = 0` past the last 1-bit, so `tau_A(m) + C_m` is always even and the
> downward recursion admits a persistent off-by-one: **a seed *below* the true carry stays
> exactly one below forever.** The measured seed-below offset is `{-1}` for `1/2, 1/4, 3/8` and
> `{0}` for every non-dyadic target... **The corpus's flagship candidate `1/2` is precisely the
> degenerate case of the transducer.**

Same mechanism, same parity argument, same three dyadic targets, same conclusion as section 82.
The timing is not ambiguous:

| | commit | timestamp |
|---|---|---|
| theirs | `60263faf3d` "the greedy is a bounded-look-ahead parity rule, with no reals in it" | **2026-08-22 13:15:07** |
| mine | `58281df518` (section 82) | 2026-08-23 06:34:35 |

`git merge-base --is-ancestor 60263faf3d 58281df518` returns true. **Seventeen hours earlier, and
in my own ancestry. Section 82 discovered nothing.**

T51b -- follow pointers before deriving -- failed here in a specific way worth naming. I did grep
before writing section 82, but I grepped for *terms*; I did not open the **named file already
sitting on my unread list**. `RunLengthMarginLawAndDivisorMultiplicity.md` has been listed as
unread in every brief since section 80. **"Unread" is not "absent" -- it is unchecked prior art,
and while it sits on the list no novelty claim in its subject area is safe.**

What section 82 still contributes, stated at its true size: a two-directional `Lstar` statistic
over thirteen targets at cap 200 where section 11 reports one seed and one length, and the T61b
correction to my own T60c. Neither is a new mechanism. **Section 82's framing is retracted; its
measurements stand as a wider replication.**

### 88.2 Section 84 survives the same check

The obvious worry is that the prime-slack theorem is also already there. It is not: `slack`,
`s(p)`, `two-valued` and `in {0,1}` return nothing from that file (calibrator in the same run:
`carry` = 37 occurrences, so the sweep ran). **Section 84's `s(p) in {0,1}` and
`s(p) = 1 iff p not in A and eps_p = 1` remain mine**, as does the `ord_q(2)` density law.

### 88.3 What section 11 has that I did not -- and it is stronger than anything I derived

The carry identity is binary addition from the least significant end, `tau_A` the input stream,
`C` the carry, `eps` the output:

    eps_m    = (tau_A(m) + C_m) mod 2
    C_{m-1}  = (tau_A(m) + C_m) div 2

and since `tau_A(m) = t_fixed(m) + 1_A(m)` with `t_fixed(m) = #{d in A : d | m, d < m}` reading
**only indices below `m`**, the output bit **forces membership**:

> `1_A(m) = ( eps_m + C_m + t_fixed(m) ) mod 2`

verified **4000/4000 at depth 4000** on ten targets. Hence section 11's conclusion, which is a
fifth equivalent form of the problem and sharper than any of mine:

> the Mersenne greedy -- defined by real comparisons `rho_{n-1} >= w_n` against irrational tails
> -- is equivalently a **parity rule with 12-step look-ahead on the divisor lattice, with no real
> numbers in it.**

Their look-ahead figures (`C <= 13` in range, seed 32, `L = 12`, exact carry recovered
1500/1500) sit consistently beside mine (`max C` 15-24 at depths 8000-30000, `Lstar_up` 6-10);
the difference is range, not disagreement.

**Status. A retraction and a genuinely new fact.** Section 82's mechanism was prior art by
seventeen hours and I should have read the file rather than grepped around it. Section 84
survives. And the greedy has a membership-forcing parity form with bounded look-ahead and no
reals in it -- which I did not have, and which is the strongest reformulation on the table.
**No progress on Erdos 257.**
