# The carry state count grows with depth (and the even-denominator half is PRIOR ART)

> **RETRACTION BANNER — read before anything below.** This note originally claimed four findings.
> **Three of them are re-derivations and are retracted as novelty:**
>
> * the even-denominator infinite look-ahead (section 2, finding B),
> * the explanation of `carry_window_automaton.py`'s outlier (section 3a),
> * the `BIG = 64` seed-floor defect in that script (section 3a).
>
> All three were already on disk. The mechanism is
> `RunLengthMarginLawAndDivisorMultiplicity.md` section 11, commit `60263faf3d`
> (2026-08-22 13:15:07): *"For dyadic `y`, `eps_m = 0` past the last 1-bit, so `tau_A(m) + C_m` is
> always even and the downward recursion admits a persistent off-by-one: a seed BELOW the true
> carry stays exactly one below forever... The corpus's flagship candidate `1/2` is precisely the
> degenerate case of the transducer."* That is verbatim my finding (B). Cross-index **T67** already
> RETRACTED a second re-derivation of it (`CertificateSocketCollapse.md` s82). Both instrument
> defects are stated in the docstring of `scripts/carry_lookahead_parity_probe.py`, which also
> **pre-registered the even-denominator hypothesis as its P2 with a falsifier**, and its receipt
> `state/formal_math/erdos257_period_noncollapse/carry_lookahead_parity_receipt.json` already has
> `n_resolved = 0 / n_unresolved = 800` for every even-`q` target (`q = 2,4,8,512,1024,...`) with
> `Lstar_up` finite at 6-7 from above — 13 targets, two seed directions, cap 200.
>
> **This is the THIRD independent re-derivation of the dyadic degeneracy in the corpus.** T67's own
> diagnosis applies to me unchanged: *"I grepped for TERMS but never opened the NAMED FILE on my
> own unread list. UNREAD IS NOT ABSENT."* I had the T67 headline in front of me in a trap listing
> earlier in the same session and did not open it.
>
> **What is NOT retracted:** finding (A), the depth-scaling of the carry STATE COUNT (section 2).
> A targeted grep found the state count measured at a single depth
> (`CertificateSocketCollapse.md:5961`, `carry_window_automaton.py` item 3) but no depth-scaling of
> it, and the parity probe ran at depth 6000 only. Treat (A) as "not located elsewhere", not as
> proven novel — this note's track record on novelty claims is 1 for 4.

Owner: `system/lib/erdos257_lambda_greedy.py` ->
`state/formal_math/erdos257_carry_lookahead_growth_receipt.json`.
Seven targets, depths `8 x 10^3` and `2 x 10^6`, zero undecided ranks.

## 0. What this corrects

**T60a (cross-index) records the opposite conclusion, and it is a DEPTH ARTEFACT.** Its author
predicted the carry look-ahead grows (from `C_m` unbounded, since `tau_A` is unbounded for every
infinite `A`), measured `L` min 7 / median 7 / max 9-12 with 12-14 distinct carry values at depth
`6000`-`8000`, and RETRACTED the prediction: *"the automaton IS effectively finite-state; the
corpus's framing was right and mine was wrong."*

**The original prediction was right.** Depth `8000` cannot see the growth. Re-measured 250x deeper
with the constant-precision engine, the state count grows on every target and the look-ahead grows
with it — and at even denominators it is not finite at all.

## 1. Definition (single instrument, used identically at every depth)

`Q_m = floor(C_m)` with `C_m = sum_{j>=1} tau_A(m+j) 2^-j`. Let
`W_L = sum_{j<=L} tau_A(m+j) 2^-j`, so `0 <= C_m - W_L <= 2^-L Cmax`. Define `L(m)` as the least
window length that DETERMINES `Q_m` from `tau_A` alone:

        L(m) = min { L :  floor(W_L) = Q_m   and   frac(W_L) + 2^-L Cmax < 1 } .

A finite-state carry rule requires `L` bounded. **Absolute `L` values here are NOT comparable to
T60a's** — that instrument is a different script with a different convention — but the GROWTH is
measured with one definition held fixed across depths and targets, which is what the question needs.

## 2. Measurement

Sampled in the top half of each run, `5 x 10^4` points per row.

| target | `q` odd | depth | `max C` | **distinct carry states** | `L` med/mean/max | unresolved |
|---|---|---|---|---|---|---|
| `1/21` | yes | `8 x 10^3` | 16 | **17** | 4 / 4.235 / 8 | 0 |
| `1/21` | yes | `2 x 10^6` | 75 | **73** | 5 / 5.174 / 10 | 0 |
| `4/9` | yes | `8 x 10^3` | 17 | **17** | 4 / 3.933 / 8 | 0 |
| `4/9` | yes | `2 x 10^6` | 75 | **72** | 4 / 4.797 / 8 | 0 |
| `3/11` | yes | `8 x 10^3` | 20 | **19** | 4 / 4.046 / 8 | 0 |
| `3/11` | yes | `2 x 10^6` | 82 | **77** | 4 / 4.795 / 10 | 0 |
| `7/31` | yes | `8 x 10^3` | 18 | **19** | 3 / 3.558 / 6 | 0 |
| `7/31` | yes | `2 x 10^6` | 80 | **73** | 4 / 4.429 / 8 | 0 |
| `1/5` | yes | `8 x 10^3` | 16 | **17** | 3 / 3.514 / 6 | 0 |
| `1/5` | yes | `2 x 10^6` | 77 | **74** | 4 / 4.474 / 8 | 0 |
| `1/2` | **no** | `8 x 10^3` | 17 | 16 | **INFINITE** | 3934 / 3934 |
| `1/2` | **no** | `2 x 10^6` | 76 | 73 | **INFINITE** | 50000 / 50000 |
| `1013/2048` | **no** | `8 x 10^3` | 19 | 19 | **INFINITE** | 3934 / 3934 |
| `1013/2048` | **no** | `2 x 10^6` | 81 | 75 | **INFINITE** | 50000 / 50000 |

**(A) The state count grows on every target**, 16-19 at depth `8 x 10^3` to 72-77 at `2 x 10^6` —
a factor of ~4 for 250x depth, uniform across all seven. It tracks `max C`, which tracks
`max tau_A / 2` (see `DefectRunningMaxDivisorLaw.md`), which is `N^{(1+o(1)) log 2 / log log N}`.
Bounded within a fixed window, unbounded in `N`. **Not finite-state.**

**(B) At EVEN denominators the look-ahead is infinite, and this is structural, not statistical.**
For `y in Z[1/2]` and `m` past the level, `{2^m y} = 0`, so `C_m` is EXACTLY an integer. The window
sum approaches it strictly from below, so `floor(W_L) = C_m - 1` for every finite `L` and the margin
clause never fires. **100% unresolved at both depths on both even-denominator targets** — 3934/3934
and 50000/50000, not a tail effect.

For odd `q` the distance from `C_m` to the integer below is `{2^m y} >= 1/q`, which is exactly what
supplies a finite `L`; the rough scale is `log2(q * max C)` (8.4 and 10.6 for `1/21` at the two
depths, against measured medians 4 and 5 — the prediction is a ceiling, as it should be).

## 3. Why it matters for the frontier

`SurvivorMechanismCensus` / T55a lists **"eventually periodic or finite-state carry rule"** as the
fifth countermodelled proof shape, and T59c names the live question as *"whether a local
finite-state carry automaton can be made compatible with a global divisor sum"*.

**On the actual counterexample candidates the local side of that question is settled negatively.**
By T57d every finite Mersenne subsum has ODD denominator, so an even-denominator target in the
achievement set has infinite support automatically — even denominators are precisely where a
counterexample can live. This note shows the carry there is **not a bounded-window function of
`tau_A` at any window length**. So the finite-state horn of T59c is unavailable exactly where it
would have been used, and (A) says it degrades with depth everywhere else too.

## 3a. This EXPLAINS T60c's recorded "UNEXPLAINED OUTLIER", on independent code

`scripts/carry_window_automaton.py` measures the same question with a DIFFERENT definition of `L`
— downward bisimulation of two seeds `0` and `BIG = 64` under `a <- (tau_A(j) + a) // 2`, taking the
least `L` at which they merge — and a separate check that the merged value equals the true carry.
T60c records a defect (the `need[m] = 99` sentinel means "not found below 40") **and an unexplained
outlier**. Running it unmodified at its default depth 6000:

| target | `q` | `L` min/median/max | window value == true carry |
|---|---|---|---|
| `1/21` | odd | 7 / 7 / 9 | **1500 / 1500** |
| `4/9` | odd | 7 / 7 / 10 | **1500 / 1500** |
| `1/465` | odd | 7 / 7 / 12 | **1500 / 1500** |
| `1/2` | **even** | **99 / 99 / 99** | **0 / 1500** |

Perfect discrimination on its four targets: the three odd denominators resolve completely, the one
even denominator fails completely. **The outlier is finding (B).** The `L = 99` sentinels are not
"not found below 40" — they are genuine infinities, and `0/1500` is the structural consequence of
`floor(W_L) = C_m - 1` at every `L`. Two instruments with two different definitions of `L`
(truncation-from-below here, downward bisimulation there) produce the same even/odd split, which is
the strongest cross-validation available for section 2.

**A second, separate instrument defect, recorded here.** That script's `L` cannot go below
`log2(BIG) = 6`: the downward recursion halves the seed gap, so seeds `0` and `64` cannot merge in
fewer than 6 steps. Its "min 7 / median 7" is therefore dominated by the choice `BIG = 64` and is
**not** a measurement of the look-ahead. T60a read `L ~ 7` off it and matched it against
`log_2(17) ~ 4.1` "plus overhead"; the agreement is with `log2(BIG)`, not with the carry. Any future
use of that script should vary `BIG` and confirm `L` is insensitive to it before quoting a value.

## 4. What this does NOT establish

* It does not touch the GLOBAL divisor side of T59c, and it proves nothing about irrationality.
  Killing the finite-state reading narrows the search; it is not progress toward the theorem.
* (B) is a statement about determining `floor(C_m)` by truncation FROM BELOW. `C_m` sitting exactly
  on an integer is a boundary phenomenon of the floor, and a different discretisation might not see
  it. What is robust is that the even-denominator carry carries no slack at all, while the odd-`q`
  carry has slack `>= 1/q`.
* Absolute `L` values are instrument-specific and must not be compared with T60a's numbers; only
  the within-instrument growth and the finite/infinite split are claimed.
* Depths are `8 x 10^3` and `2 x 10^6`. `ProgrammeSpine.md` section 12 (K1) still applies: finite
  depth certifies nothing about membership.

## 5. Reproduce

```
./repo-python -c "
import sys; sys.path.insert(0,'.')
from system.lib.erdos257_lambda_greedy import greedy_lambda
import numpy as np
r = greedy_lambda(1, 2, 2_000_000, J=160, tau_max=1<<16)   # even denominator
Q = r['carry'].astype(np.int64)
print('carry is an exact integer at every rank past the level:', r['first_death'], len(r['undecided']))
print('distinct carry states:', len(np.unique(Q[100:])), ' max:', int(Q.max()))
"
```
Full instrument and the `L` loop: `state/formal_math/erdos257_carry_lookahead_growth_receipt.json`
records the definition, per-row counts and the unresolved fractions.
