# Strict-record reset and repair at the denominator-21 source

Status: ordinary deduction plus exact finite computation, 2026-08-22.  The
record-reset and record-repair inequalities below are open.  This note does
not prove that `1/21` belongs to the Mersenne achievement set and does not
decide Erdős 257.

## 1. The computational signal

Let `b_n` be the denominator-21 greedy word, let

\[
 t_n={\bf 1}_{n\equiv 0,5\pmod 6},\qquad
 f(n)=\sum_{d\mid n}b_d,
\]

and let `Q_n` be the exact Lambert defect.  The checked recurrence is

\[
 Q_n=2Q_{n-1}+t_n-f(n),\qquad Q_0=0.       \tag{1}
\]

Call `n` a strict record rank when

\[
 Q_n>\max_{0\le j<n}Q_j.
\]

The strongest observed statement is the bounded reset

\[
 \boxed{Q_{n+1}\le 4.}                              \tag{RB4}
\]

The same experiment also tests the weaker repair statement

\[
 \boxed{f(n+1)\ge Q_n+t_{n+1}.}             \tag{RR}
\]

By (1), `(RR)` is equivalent to `Q_(n+1)<=Q_n`.  Thus every new defect spike
would pay enough selected-divisor load at the next rank to prevent two
consecutive record increases.  The stronger `(RB4)` says that each spike is
followed by a return to one fixed bounded band.

The exact canonical quotient-greedy replay through rank `500002` has 34 strict
record ranks, no failure of `(RR)`, and no successor defect above `4`.  The
last record in this range is

\[
 n=480479,\qquad Q_n=52,
\]

while the successor has

\[
 f(480480)=101,qquad t_{480480}=1,qquad Q_{480480}=4.
\]

The corresponding margin in `(RR)` is `48`.  Through rank `200000`, where the
existing independent dyadic greedy checker has already identified the same
itinerary, the last record is

\[
 n=180179,qquad Q_n=40,qquad f(180180)=79,qquad Q_{180180}=2.
\]

The record successors are empirically highly divisor-rich.  A representative
part of the exact output is:

| record `n` | `Q_n` | `n+1` | `tau(n+1)` | `f(n+1)` | `Q_(n+1)` |
|---:|---:|---:|---:|---:|---:|
| 2519 | 11 | 2520 | 48 | 22 | 1 |
| 5039 | 14 | 5040 | 60 | 27 | 2 |
| 10079 | 18 | 10080 | 72 | 35 | 2 |
| 55439 | 29 | 55440 | 120 | 57 | 2 |
| 110879 | 36 | 110880 | 144 | 72 | 1 |
| 180179 | 40 | 180180 | 144 | 79 | 2 |
| 360359 | 51 | 360360 | 192 | 102 | 1 |
| 480479 | 52 | 480480 | 192 | 101 | 4 |

This table is evidence for theorem selection, not evidence that the displayed
pattern continues.

### Two-million-rank falsification checkpoint

An exact detached replay through rank `2000002` produced five further strict
records and no failure of either candidate.  The full run has 39 strict
records.  Its maximum defect is

\[
 Q_{1441439}=75.
\]

The new records are:

| record `n` | `Q_n` | `n+1` | `tau(n+1)` | `f(n+1)` | `Q_(n+1)` | dyadic record parent |
|---:|---:|---:|---:|---:|---:|---:|
| 655199 | 56 | 655200 | 216 | 110 | 3 | 327599 |
| 720719 | 62 | 720720 | 240 | 123 | 2 | 360359 |
| 1053359 | 64 | 1053360 | 240 | 128 | 1 | none |
| 1081079 | 66 | 1081080 | 256 | 131 | 2 | none |
| 1441439 | 75 | 1441440 | 288 | 149 | 2 | 720719 |

Here a dyadic record parent means that `n=2r+1` and `r` is itself a strict
record.  Thus the larger run adds both propagation events and two genuinely
new root records.  It does not merely repeat the same record chain at a longer
horizon.

All 18 dyadic parent-child record links through this checkpoint satisfy the
stronger inherited-load inequality

\[
 \boxed{f(r+1)\geq Q_{2r+1}+t_{2r+2}.}              \tag{DI}
\]

The minimum inherited margin on those links is three.  The three new links
have margins 34, 39, and 47, respectively.  Since
`r+1` divides `2r+2`, inequality `(DI)` implies `(RR)` at the child using only
divisor inclusion: no newly selected divisor of `2r+2` is needed for the
repair.  This isolates dyadic propagation as a producer and leaves root-record
birth as a separate arithmetic mechanism.

The exact receipt is
`state/formal_math/erdos257_period_noncollapse/twenty_one_computational_structure_receipt_2000002.json`.
It has payload digest
`c3b2d899da07d668fcd712e342b83648d63c3b8cae15235ba007dc55ae6ea7b7`
and records the producer script digest
`aec79602a04ccdcc5bd347be2be95aaf793888b8e20958ee55d4f6f09bb96d9e`.
Its first 34 record rows agree exactly with the canonical rank-`500002`
receipt, and its independent rank-`200000` itinerary agrees with
`check_twenty_one_greedy.py`.  Recompute and compare the same parameterized
receipt with

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/\
  twenty_one_computational_structure_lab.py \
  --ranks 2000002 --window-scales '' \
  --check state/formal_math/erdos257_period_noncollapse/\
twenty_one_computational_structure_receipt_2000002.json
```

This is still finite falsification evidence.  Its mathematical contribution
is that `(RB4)` and `(RR)` survived five new opportunities to fail, while the
record genealogy separated into a dyadically inherited class governed by
`(DI)` and a root class requiring a different source-sensitive argument.

## 2. Why either record statement would solve the target

First assume `(RB4)` at every strict record rank.  If there are infinitely many
strict records, their successors give cofinally many returns to `Q<=4`.  If
there are only finitely many strict records, then `Q` is globally bounded by
the last record value.  In either case the checked cofinally-bounded-defect
consumer proves `1/21` membership.

There is also a quantitative fallback.  Assume `(RR)` at every strict record
rank.  Fix `N`, and choose a strict record rank `r<=N` at which the running
maximum of `Q` through `N` is first attained.  Then

\[
 Q_N\le Q_r\le f(r+1)\le \tau(r+1).
\]

Pairing divisors below and above the square root gives the elementary estimate

\[
 \tau(m)\le 2\lfloor\sqrt m\rfloor.
\]

Consequently

\[
 Q_N\le 2\sqrt{N+1}                              \tag{2}
\]

at every rank.  In particular `(Q_N+1)/2^N` tends to zero.  The existing
Lean-checked theorem
`one_div_twenty_one_mem_mersenneAchievementSet_of_defectSubexponential`
would then give

\[
 \frac1{21}\in\texttt{mersenneAchievementSet}.
\]

The checked finite-support exclusion would make the resulting support
infinite and hence would disprove the universal assertion in Erdős 257.

These implications are the reason to study only strict record ranks.  They
replace an all-rank reservoir inequality by a sparse arithmetic supply theorem
and use the divisor function only after the selected-divisor load has been
forced at those ranks.

## 3. Relation to the existing square-root theorem

Lean already proves a square-root defect estimate at skipped positive ranks.
That theorem does not cover the present computation: several strict record
ranks are selected, including `79`, `419`, `839`, `2519`, `5039`, `10079`,
`15839`, `32759`, `110879`, `180179`, `327599`, and `332639` in the audited
range.

The record-reset route would give cofinal bounded returns directly.  The
record-repair fallback would extend square-root control to every rank without
requiring a bound on the length of a selected run.  Both are genuine producers
if proved, not another normalization of membership.

## 4. Adversarial boundary

The statement is not a formal consequence of recurrence (1), Booleanity, or
nonnegative defect.  For the cofinite control word `b_n=1` for `n>=7`, the
same source recurrence has a strict record at `n=5` with

\[
 Q_5=1,qquad f(6)=0,qquad t_6=1,
\]

so `(RR)` fails by two units.  Any proof must use the actual greedy
take/skip comparison together with the divisor ancestry of the same word.
The same control has `Q_7=5` and `Q_8=9`, so `(RB4)` fails as well.

There is also no assertion here that record successors are highly composite
in the ordinary number-theoretic sense.  The finite data show a strong
alignment with divisor-rich successors; `(RR)` asks only for enough *selected*
divisors to dominate the defect.

## 5. Next proof-producing throat

The preferred theorem is

> If `n` is a strict record rank of the actual denominator-21 greedy defect,
> then `Q_(n+1)<=4`.

Its weaker fallback is

> If `n` is a strict record rank of the actual denominator-21 greedy defect,
> then `f(n+1)>=Q_n+t_(n+1)`.

A fixed additive weakening

\[
 Q_n\le f(n+1)+C
\]

at strict record ranks would still give `Q_N=O(sqrt N)` and would be equally
sufficient for the checked subexponential consumer.  This is the preferred
fallback if exact next-step nonincrease is too rigid.

The immediate falsifier for `(RB4)` is one strict record followed by defect at
least five; the falsifier for `(RR)` is a negative repair margin.  The script
reports every record, its successor factorization, total and selected divisor
loads, next defect, and repair margin:

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/\
  twenty_one_computational_structure_lab.py --write
```

The canonical receipt is
`state/formal_math/erdos257_period_noncollapse/twenty_one_computational_structure_receipt.json`.
It binds the script hash, exact parameters, Python version, analysis paths,
checked Lean consumers, every strict-record row, explicit nonclaims, and a
canonical payload digest.  Schema `v1` also stores the complete itinerary as a
base64 little-endian rank bitset, rather than only its digest.  Downstream
divisor and genealogy probes can therefore recover every selected rank without
rerunning the expensive quotient recurrence.

### Cofinal repair is enough

[`RecordCofinitenessBoundary.md`](RecordCofinitenessBoundary.md) proves a
weaker endpoint than either all-record conjecture above.  If the `1/21` orbit
has a final skip, the positive homogeneous defect eventually dominates the
linear divisor load, and every sufficiently late rank becomes a strict
record.  Hence it is enough to produce arbitrarily late ranks `N` satisfying

\[
 f(N)\ge Q_{N-1}+t_N,
\]

because each is a non-record.  This statement is cofinal rather than uniform
and need not occur immediately after an existing record.  Exact fatal-gap
splices confirm the opposite behavior: after a finite transition, every rank
is a record and all record phases occur.

The same receipt stores `P`, `R`, and `F` at every record, plus a dyadic
inheritance table for every strict parent whose child lies in range.  The table
links `(DI)` to the child-record `(RR)` consequence and lists the complementary
root records explicitly.  Its `analysis_lineage` section maps each of `RB4`,
`RR`, and `DI` to the motivating note, machine field, analytic consequence,
and checked Lean consumers.  Thus the computation points to the analysis that
asked for it, and the analysis points back to the exact machine evidence and
consumer.

The follow-on genealogy analysis
[`TwentyOneRecordAncestorInheritance.md`](TwentyOneRecordAncestorInheritance.md)
uses the immutable two-million-rank receipt to widen `(DI)` beyond direct
dyadic children.  It tests arbitrary earlier record successors dividing the
current successor and isolates the finite additive-eight candidate `(AI8)`,
whose all-depth form would imply the same checked square-root defect bound.

The rank-`2000002` receipt above is the immutable schema-`v0` terminal result
from before this infrastructure upgrade; commit `3900ab8` binds it to the
exact producer script digest printed above.  A future deliberate deep replay
can emit the richer schema, but the existing six-minute result is not rerun
merely to change packaging.

Recompute and compare the canonical receipt with

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/\
  twenty_one_computational_structure_lab.py --check
```

The same script continues to audit the delayed-density reservoir and sliding
replenishment windows, but those measurements are secondary to `(RB4)` and
`(RR)`.
