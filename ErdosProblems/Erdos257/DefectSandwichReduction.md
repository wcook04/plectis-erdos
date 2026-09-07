# The defect sandwich: a sharp alive-prefix diagnostic, not a DRMH reduction

Owner: `system/lib/erdos257_lambda_greedy.py` ->
`state/formal_math/erdos257_defect_sandwich_reduction_receipt.json`.
Target `y = 1/21`, certified depth `8 000 000`, zero undecided ranks, 23 s.

Sibling: `DefectRunningMaxDivisorLaw.md` (same session, landed `23c79c338f`/`79c4fcd1ef`) has
(L1)-(L4) and the first reduction. That note's section 3 calls the upper bound on `Q` "the
circular one", which is correct for induction on the recurrence. An earlier revision of THIS
note claimed to have given a non-circular replacement reaching the all-depth Lean socket.
**That claim was wrong twice over and both errors are recorded below:** the bound carries an
ALIVENESS premise, so it reaches only a finite alive prefix (section 2), and its constant is 2,
not 1 (CORRECTION, section 1). What survives is a sharp diagnostic, not a reduction.

## 1. The sandwich (PROVED, unconditional algebra + aliveness)

Write `r_N = y - sum_{a in A, a<=N} 1/(2^a - 1)` and `f_N = 2^N r_N`. Pure algebra, with no
membership hypothesis anywhere:

        C_N  =  2^N (y - sum_{m<=N} tau_A(m) 2^-m)  =  f_N + D_N ,

        D_N  :=  sum_{j>=1} 2^-j  #{ a in A, a <= N : a | N+j } .

`D_N` involves **only the already-selected support** `A cap [1,N]` — no future, no assumption
that the representation closes. Aliveness at rank `N` is exactly `0 < f_N <= 2^N T_N`, with
`2^N T_N = 1 + 2^-N/3 + O(4^-N)`. Hence, for every rank at which the greedy is alive,

        floor(D_N)  <=  Q_N = floor(C_N)  <=  floor(D_N) + 2 .

**CORRECTION (self-caught, same session).** An earlier revision of this note stated the upper
bound as `floor(D_N) + 1` and labelled it PROVED. **That constant is wrong.** The derivation
gives `C_N in (D_N, D_N + 2^N T_N]` with `2^N T_N = 1 + 2^-N/3 + ...`, so `floor(C_N)` reaches
`floor(D_N) + 2` whenever `frac(D_N) >= 1 - 2^-N/3`. **The proved constant is 2.**

The `+1` form is a property of `y = 1/21`, not a theorem: for that target the difference
`Q_N - floor(D_N)` is `0` at 33.4% of ranks and `1` at 66.6% and never 2, **verified at every
rank to depth `8 x 10^6`** — but a sweep of ~6000 targets over
`q in {4,5,8,9,11,16,21,31,32,63,64,127,128,255,1024,2048}` finds `Q_N - floor(D_N) = 2` at an
ALIVE rank, first at `y = 5/4`. Quote the `+1` only as a measured fact about `1/21`.

**The contrapositive is NOT a sound death test either.** `Q_N - floor(D_N) >= 2` fired on 294
of 2534 surviving targets in that sweep, because those are exactly the legitimate `+2` cases.
With the corrected threshold (`>= 3`) the test is sound but lags badly, and it is not sharper
than the tail comparison the engines already run. Do not use it as a death certificate.

**Why this is not the circular bound.** The circular argument induces on
`Q_N = 2 Q_{N-1} + t_N - tau_A(N)` and degrades by `tau(N) - tau_A(N)` per step. The sandwich
does not induct at all: it is one identity plus the aliveness interval, and it pins `Q_N` to a
quantity computable from the past.

## 2. What the sandwich does and does not reduce

With `M(d) := max_{m<=d} tau_A(m)` and `H(M) = max(1, 1 + max_{N<M} Q_N)`:

* **(P1)** `2 H(d) >= 1 + M(d)` — **now MACHINE-CHECKED**, not prose. A concurrent Codex
  session (`codex-erdos257-staircase-20260823`) formalised it while this note was being
  written, in `TwentyOneSelectedDivisorHeightReduction.lean` (verified on disk this pass,
  no `sorry`): `twentyOneSelectedDivisorLoad_le_two_defect_add_one` (:40) and
  `twentyOneSelectedDivisorHeight_add_one_le_two_defectHeight` (:56), over
  `twentyOneSelectedDivisorHeight d = max_{m<=d} supportCoeff(A,m) = M(d)`.
* **(S)** *(this note)* at an **alive** rank, `Q_N <= floor(D_N) + 2` (constant 2 is the
  proved one; see the CORRECTION in section 1).
* **(P3-floor)** *(measured)*
  `max_{N<2d} floor(D_N) + 1 <= M(d)`.

For one fixed `d`, **if every rank `N<2d` is already known alive**, then (S) and
(P3-floor) give

    H(2d) <= 3 + max_{N<2d} floor(D_N)      [with the corrected constant 2 in (S)]

The conclusion has the same numerical shape as the Lean socket
`TwentyOneSelectedDivisorHalfRangeBound` (:82), but this is **not** an implication to that
all-depth socket. Supplying the alive premise for every `d` is already greedy survival, hence
already the desired membership statement. After a fatal rank the scaled remainder grows
geometrically and the sandwich fails, even though `D_N` still depends only on the past support.
Thus the sandwich removes circularity from a finite alive-prefix estimate; it does not remove
circularity from the induction needed to prove aliveness.

The genuinely non-circular companion result is (P1):
`TwentyOneSelectedDivisorHeightReduction.lean` reduces DRMH to the unconditional all-depth
upper socket `H(2d) <= M(d)+1`. The sandwich does not prove that socket.

**(P3-floor) is verified with zero failures for every `d` in `[5, 4 x 10^6]`.** The only exceptions
are `d in {1,2,3,4}`, a finite seed set on which DRMH holds by direct evaluation. Slack grows:

| `d` | `10^4` | `10^5` | `10^6` | `2 x 10^6` | `4 x 10^6` |
|---|---|---|---|---|---|
| `M(d) - max_{N<2d} floor(D_N) - 1` | 11 | 23 | 47 | 63 | 65 |

## 3. What the measured floor statistic actually is

`max_{N<X} floor(D_N)` is pinned to half the divisor record, because the `j = 1` term carries weight
`1/2` and dominates:

| `X` | `10^4` | `10^5` | `10^6` | `4 x 10^6` | `8 x 10^6` |
|---|---|---|---|---|---|
| `max_{N<X} floor(D_N)` | 15 | 32 | 62 | 85 | 106 |
| `ceil(max_{m<=X} tau_A(m) / 2)` | 16 | 32 | 62 | 86 | 106 |

Equal at three of the five scales, off by one at the other two — so
`max_{N<X} floor(D_N) = max_{m<=X} tau_A(m)/2 + O(1)`, measured, not proved. Even a proof of
this estimate would control `Q_N` only while rank `N` is alive. Ignoring that obstruction, the
associated divisor-record comparison is

* **(D2)** `max_{m<=2d} tau_A(m)  <=  2 max_{m<=d} tau_A(m) - 2` .

Measured: 19 failures, **all at `d <= 20`**; slack 22 at `d = 10^4`, 47 at `10^5`, 95 at `10^6`,
130 at `4 x 10^6`.

## 4. The exact reason this is not already a theorem

For the FULL divisor function the same doubling is two lines, and the control run confirms
**zero failures**:

> For `m <= 2d` let `p` be its least prime factor. If `p = 2` then `m/2 <= d` and
> `tau(m) = tau(m/2)(e+1)/e <= 2 tau(m/2)`. If `p >= 3` then `m/p <= 2d/3 <= d` and again
> `tau(m) <= 2 tau(m/p)`. Either way `tau(m) <= 2 max_{m'<=d} tau(m')`.

**That proof does not transfer to `tau_A`.** It rests on `tau(m) <= 2 tau(m/p)`, and the
`tau_A` analogue is false: writing `m = 2^e u` with `u` odd,

        tau_A(m) = tau_A(m/2) + #{ a in A : a = 2^e v, v | u } ,

and the second term is a count of divisors of `m` at exact 2-adic valuation `e`, which is
bounded by `tau(u)` and by NOTHING in terms of `tau_A(m/2)` — membership of `2^e v` in `A` is
unrelated to membership of its half. So (D2) is a genuine statement about THIS support, and it
is where the remaining content of DRMH sits.

**The shape of what is needed:** `A` has density `1/2` and its elements are spread, so a
record-`tau_A` number at scale `2d` cannot concentrate its `A`-divisors at one 2-adic level.
That is the missing input, and it is an arithmetic statement about the greedy support, not a
dynamical one.

## 4a. The alive-prefix statistic descends to one local arithmetic statement

(P3-floor) is not the end of the descent. Three further measured steps, each verified to depth
`8 x 10^6` with its constant made explicit, reduce that **alive-prefix statistic** to a statement
about a single number's divisor lattice. They do not remove the alive premise from (S).

**Step 1 — only RECORDS matter.** `M` is non-decreasing, so `M(2d) > M(d)` only when a
`tau_A`-record falls in `(d, 2d]`; otherwise `M(2d) = M(d) <= 2M(d) - 4` for `M(d) >= 4`. There
are just **56 records below `8 x 10^6`**.

**Step 2 — at a record, only the TOP 2-ADIC LEVEL matters.** Write a record as `m* = 2^e u`
with `u` odd. Its divisors split into `e+1` levels by `v_2`, each level a copy of `div(u)`. With
`c_i := #{v | u : 2^i v in A}` we have `tau_A(m*) = sum_i c_i` and `tau_A(m*/2) = sum_{i<e} c_i`,
so `tau_A(m*) <= 2 tau_A(m*/2) - 4` is EXACTLY `2 c_e + 4 <= tau_A(m*)`.

* **(T4)** for every `tau_A`-record `m* = 2^e u` with `m* > 420`:  `2 c_e + 4 <= tau_A(m*)`.

**Verified: 8 failures among the 56 records, all at `m* in {5,10,20,40,80,120,160,420}`.**
The margin is not marginal — `2 c_e / tau_A(m*)` has min `0.2471`, median `0.4043` over the
records, against the `1` it must beat. The reason is that the level profile is FLAT:

| `m*` | `e` | `c_0 .. c_e` | `c_e / sum_{i<e} c_i` |
|---|---|---|---|
| `1441440` | 5 | `26, 27, 26, 23, 21, 26` | 0.2114 |
| `2882880` | 6 | `26, 27, 26, 23, 21, 26, 21` | 0.1409 |
| `6486480` | 4 | `43, 41, 42, 42, 39` | 0.2321 |
| `7207200` | 5 | `36, 37, 37, 32, 30, 40` | 0.2326 |

**CORRECTION 2 (self-caught, same session): the flat profile is NOT a law about greedy
supports, and the mechanism proposed in section 4 is REFUTED.** Section 4 explains (T4) by
"`A` has density `1/2` and its elements are spread, so a record cannot concentrate its
`A`-divisors at one 2-adic level". Running the same measurement on eight flagship targets at
depth `1.5 x 10^6` kills that explanation:

| target | records | `e` range | worst `c_e / sum_{i<e} c_i` | median | (T4) failures, `m* > 420` |
|---|---|---|---|---|---|
| `1/21` | 47 | 0–6 | 1.0000 | 0.2937 | **0** |
| `4/9` | 41 | 1–7 | 1.0000 | 0.3492 | 0 |
| `1/2` | 46 | 1–6 | **2.0000** | 0.3000 | **1** |
| `3/11` | 50 | 0–6 | 1.0000 | 0.2525 | 0 |
| `7/31` | 40 | 0–8 | 1.0000 | 0.3636 | 0 |
| `1013/2048` | 42 | 1–7 | **2.0000** | 0.2381 | **1** |
| `1/5` | 41 | 0–6 | 1.3333 | 0.2727 | 0 |
| `90/511` | 41 | 0–5 | 1.0000 | 0.3333 | 0 |

For `1/2` and `1013/2048` the top level carries **twice** the rest combined — the opposite of
flat — and both failures are at the SAME record, `m* = 630 = 2^1 x 315`:

    y = 1/2       : levels [6, 7],   c_e = 7,  tau_A = 13   (need 2*7 + 4 <= 13)
    y = 1013/2048 : levels [8, 11],  c_e = 11, tau_A = 19   (need 2*11 + 4 <= 19)

`e = 1` is exactly the configuration flagged two paragraphs below as dangerous and then
dismissed. **The dismissal was drawn from `1/21`'s records only.** At `e = 1` the requirement is
`c_1 <= c_0 - 4` with `c_0, c_1` both `~ tau(u)/2`, i.e. a coin flip — and these two targets lose
it. So (T4) is a statement about the `1/21` support specifically, true there to depth
`8 x 10^6` because its records happen to avoid `e = 1` above the seed set. That is a
target-specific accident, **not a mechanism**, and the density-`1/2` spread argument does not
supply one. Do not carry section 4's "shape of what is needed" paragraph forward as an
explanation; it has been tested and it is wrong.

Every 2-adic level carries about the same number of `A`-elements, `~ tau(u)/2`. Records also
sit at `e = v_2(m*) in [2,6]` (54 of 56; the `e <= 1` cases are `m* = 5` and `m* = 10`), so the
dangerous `e = 1` configuration — where `c_1 <= c_0 - 4` would be a coin flip — does not occur
above the seed set.

**Step 3 — the passage from `D` to `tau_A`, with the honest constant.**

* **(W2-floor)** for every audited `X`:
  `2 max_{N<X} floor(D_N) <= max_{m<=X} tau_A(m) + 2`.

**Zero failures to `8 x 10^6`.** The constant is 2, not 1: with `+1` it fails on the band
`X in [13860, 47879]` with worst excess exactly 1. Do not quote `2 max D <= M`.

**The assembled alive-prefix chain, with every constant explicit:**

    (T4)  [records, m* > 420]                     2 c_e + 4 <= tau_A(m*)
      ==> (D4)  [d > 239]                         M(2d) <= 2 M(d) - 4
      +   (W2-floor) [audited X, 0 failures]       2 max floor(D_N) <= M(2d) + 2
      ==>                                         max floor(D_N) <= M(d) - 1
      ==> (P3-floor)                              max floor(D_N) + 1 <= M(d)
      +   (S) [only when all N<2d are alive]      Q_N <= floor(D_N) + 1
      ==> H(2d) <= M(d)+1                         for that already-alive prefix only.

The last line is not `TwentyOneSelectedDivisorHalfRangeBound`: that Lean socket is
unconditional and quantifies over the canonical defect even after a hypothetical fatal rank.
Consequently (T4), even if proved at every record, would establish a sharp divisor statistic
but would not by itself prove membership or refute Erdős #257.

`(D4)` has 149 failures, **all at `d <= 239`**; the composite premise `(D4) and (W2)` holds at
`3 999 851` of the `3 999 996` values `d in [5, 4 x 10^6]`, the 145 exceptions being exactly
those small `d`. Finite checks below `d = 239` and `m* = 420` discharge them.

**What (T4) is, in words.** *At every record of the selected-divisor count, the top 2-adic
level of that number's divisor lattice contains fewer than half of its `A`-divisors.* That is a
local, arithmetic, checkable statement about one integer at a time — no running maxima, no
orbit, no dynamics. It replaces "a doubling law for a running maximum of a running maximum".

## 5. Standing caveats

* **The sandwich holds only while alive.** It says `alive at N ==> Q_N <= floor(D_N)+1`. It does
  NOT imply `TwentyOneSelectedDivisorHalfRangeBound`, because that socket also controls a
  hypothetical post-death tail. It removes circularity from the finite-prefix bound, not from
  the induction that would close 257.
* `ProgrammeSpine.md` section 12 (K1): survival is never implied by an open condition on `y`,
  so no depth certifies membership. `8 x 10^6` is measurement.
* `max_{N<X} floor(D_N) = max tau_A / 2 + O(1)` is MEASURED at five scales. (P3-floor) does not
  depend on it, but neither statement supplies post-death defect control.
* (D2) fails at 19 small `d`; any proof must carry an explicit `d_0` and a finite check below it.
  The sharper (D4) fails at 149 values, all `d <= 239`; (T4) at 8 records, all `m* <= 420`.
* **The flat level profile is MEASURED on 56 records, not proved**, and it is the whole content
  of (T4). It says `A` does not concentrate on one 2-adic level of a divisor lattice. Nothing
  here derives that from the greedy rule — it is the missing arithmetic input, now localised.
* The divisor chain is a reduction of the measured alive-prefix statistic, not a reduction of
  the all-depth Lean socket. Every arithmetic link is verified only to `8 x 10^6`. Erdős 257
  remains open.
* The `1/21` greedy support is not a finite Mersenne sum (`SupportWordStructureLab.md` 4g.1:
  `q = 21` admits exactly `10/21` and `31/21`), so survival forever really would give infinite
  support and refute 257.

## 6. Reproduce

```
./repo-python -c "
import sys; sys.path.insert(0,'.')
from system.lib.erdos257_lambda_greedy import greedy_lambda
import numpy as np
r = greedy_lambda(1, 21, 8_000_000, J=160, tau_max=1<<16)
print('undecided', r['undecided'], 'death', r['first_death'])
"
```
The `D_N` instrumentation is a five-line addition to the engine loop. The recorded integer
`W >> J` is `floor(D_N)`, not the real number `D_N`; the receipt records the full finite
verification.
