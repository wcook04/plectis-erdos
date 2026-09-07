# The 1/21 defect running maximum tracks the maximal divisor function

Owner: `system/lib/erdos257_lambda_greedy.py` ->
`state/formal_math/erdos257_defect_running_max_divisor_law_receipt.json`.
Target `y = 1/21`, certified depth `4 000 000`, zero undecided ranks, 12.0 s.

## 0. Why this note exists

`TwentyOneDefectDoublingHeightBound` (DRMH) is the producer currently closest to proof:

> **(DRMH)** for every `d`, `H(2d) <= 2 H(d)`, where `H(0) = 1` and
> `H(N+1) = max(H(N), Q_N + 1)`, and `Q_N` is the greedy defect of `1/21`.

The Lean chain in `TwentyOneRunningMaximumProducer.lean` proves DRMH is sufficient for
`1/21 in mersenneAchievementSet`, hence for an infinite rational representation, hence for
Erdos 257 being FALSE. Until now DRMH read as an opaque dynamical inequality about a running
maximum. **It is not. `H` tracks the maximal divisor function, and the constant is pinned.**

## 1. The measurement

Certified to depth `4 x 10^6` (previous deepest DRMH evidence: none recorded; the deepest
`1/21` orbit on file is the rank-`2 x 10^7` run used for the primorial-repair audit, which
did not evaluate `H`).

| quantity | value |
|---|---|
| DRMH violations, `1 <= d <= 2 000 000` | **0** |
| DRMH minimum slack `2H(d) - H(2d)` | **0**, attained at `d = 4` **only** |
| strict records of `Q` | 42 (excluding the seed) |
| record successors divisible by 4 (FAPL4) | **42 / 42** |
| `max Q` | 86 |

The `d = 4` zero is an **equality**, not a violation: DRMH is TIGHT at the seed and nowhere
else in range. Any proof must therefore be non-strict, and any strict variant is already
false at `d = 4`.

## 2. What actually drives `H` — three laws, all measured

**(L1) Every strict record sits one below a DIVISOR-RICH number.** The last twelve record
successors are `180180, 205920, 221760, 327600, 332640, 360360, 480480, 655200, 720720,
1053360, 1081080, 1441440`, with `tau` between 144 and 288. **Careful — they are not all
highly composite: exactly 17 of the 42 set a new record for `tau`**, the rest (e.g. `180180`,
`205920`, `327600`, `360360`, `480480`, `655200`, `1053360`, `2106720`) are merely
divisor-rich. So (L1) is "large `tau(N+1)`", not "HCN"; a proof keyed to the HCN ladder would
be keyed to the wrong set. The mechanism is immediate from
`Q_N = floor(sum_{j>=1} tau_A(N+j) 2^-j)`: the `j = 1` term dominates and it is
`tau_A(N+1)/2`. **FAPL4 then follows** from these successors all being divisible by 4, which
is a property of divisor-rich numbers rather than an independent dynamical fact.

**(L2) At every record, `Q_N` is one quarter of `tau(N+1)`.**

    4 Q_N / tau(N+1)  in  [0.979, 1.139]   over all 42 records.

**(L3) `H(N)` is a constant times the maximal divisor function.** With
`maxtau(N) = max_{m<=N} tau(m)`:

| `N` | `2^8` | `2^12` | `2^16` | `2^18` | `2^20` | `2^21` |
|---|---|---|---|---|---|---|
| `H(N)/maxtau(N)` | 0.2500 | 0.2917 | 0.2667 | 0.2619 | 0.2625 | 0.2639 |

The ratio OSCILLATES in `[0.2619, 0.2917]` over `2^8..2^21` with no monotone trend (it is
0.2917 at both `2^9` and `2^12`, 0.2619 at `2^18`, 0.2639 at `2^21`). What is measured is
BOUNDEDNESS in that band, not convergence — do not quote a limiting constant. So
`H(N) = Theta(maxtau(N))` in range, i.e. `N^{(1+o(1)) log 2 / log log N}` — **not** `O(log N)`,
and not linear either.

**(L4) The defect is exactly half its a-priori divisor ceiling.** With
`U(N) = sum_{j>=1} tau(N+j) 2^-j` (the largest `Q_N` could be if `A` were all of `N`):

    Q_N / U(N)  in  [0.478, 0.523],  mean 0.488, over all 42 records.

That is the density-`1/2` fact for the greedy support, localised at the records.

## 2a. The reduction — DRMH follows from ONE inequality, and half of it is free

**(P1) PROVED, from the aliveness invariant alone.** The defect obeys
`Q_{N+1} = 2 Q_N + t_{N+1} - tau_A(N+1)` and `Q_{N+1} >= 0`, hence

        2 Q_N  >=  tau_A(N+1) - t_{N+1}  >=  tau_A(N+1) - 1 .

No membership hypothesis is used — only `Q >= 0`, which is the definition of the orbit being
alive. Verified at **4 000 000 / 4 000 000** ranks. Since
`H(M) = max(1, 1 + max_{N<M} Q_N)`, taking the max over `N < d` gives

        H(d)  >=  1 + (max_{m<=d} tau_A(m) - 1)/2 ,   so   2 H(d)  >=  1 + max_{m<=d} tau_A(m).

**This bound is TIGHT, not slack:** `min_d H(d)/(max tau_A(d)/2) = 1.0000`, median `1.0201`.
`H` *is* the running maximum of `tau_A/2`, to within 2%. That is the exact content of (L3):
`maxtau_A ~ maxtau/2` by the density-`1/2` fact, so `H ~ maxtau/4`, which is the measured
`0.26`.

**(P2) the remaining obligation.** Substituting the above into DRMH, it suffices that

        (P2)      max_{N < 2d} Q_N   <=   max_{m <= d} tau_A(m) .

> **(P1) + (P2) ==> DRMH ==> `1/21 in mersenneAchievementSet` ==> Erdos 257 is FALSE.**

The reduction is now formalized without a finite-max encoding gap in
`TwentyOneSelectedDivisorHeightReduction.lean`.  It defines recursively

    S(0) = 0,
    S(d+1) = max(S(d), tau_A(d+1)),

and Lean proves

    tau_A(N+1) <= 2 Q_N + 1,
    S(d) + 1 <= 2 H(d).

The single remaining producer is named
`TwentyOneSelectedDivisorHalfRangeBound`:

    H(2d) <= S(d) + 1.

Lean composes it with the proved lower comparison to obtain DRMH and the
final negation of universal irrationality as
`not_universal_of_twentyOneSelectedDivisorHalfRangeBound`.  Thus P1 is no
longer merely a prose inference from aliveness, and P2 is an exact
consumption-ready theorem socket.  No theorem in that module proves P2.

**(P2) is verified for every `d` in `[1, 2 000 000]` except `d = 4`** — a single seed exception,
and exactly the `d` at which DRMH itself has slack `0`. So `d <= 4` is a finite check (DRMH
holds there by direct evaluation) and the whole producer reduces to (P2) for `d >= 5`.
Slack is large and growing: `max tau_A - max Q` is `48` at `d = 10^6` and `63` at `d = 2x10^6`.

**Why this is worth having.** DRMH is a doubling law for a running maximum of a running
maximum, which is an awkward object to attack. (P2) has no nested maxima: it compares the
defect directly against the selected-divisor count, at half the range. The hard direction is
now isolated and named — an UPPER bound on `Q`, which is the circular one (section 3).

## 3. What this reframes

Substituting (L3) into DRMH:

> DRMH is, up to the constant in (L3), the statement
> `maxtau(2d) <= 2 maxtau(d)` — **which is classical** (`tau(2u) <= 2 tau(u)`, so the even
> `m <= 2d` are covered by `m/2 <= d`).

So DRMH is not asking for a new dynamical estimate. It is asking for **explicit two-sided
constants in (L3)**: an upper bound `H(2d) <= c_1 maxtau(2d)` and a lower bound
`H(d) >= c_2 maxtau(d)` with `c_1 <= 2 c_2`. The measured ratio sits at `0.26` with spread
under `0.03` across five decades, so the required constants are not tight — the difficulty is
entirely that BOTH bounds quantify over the greedy's own divisor selection.

**The honest boundary.** The upper bound is the circular one. Induction on
`Q_N = 2Q_{N-1} + t_N - tau_A(N)` gives, using `2U(N-1) = tau(N) + U(N)`,

    Q_N <= U(N) + 1 + (tau(N) - tau_A(N)),

so the bound degrades by the number of divisors of `N` the greedy did NOT select. Closing
that is exactly "the greedy selects a positive proportion of divisors", i.e. the local-carry
vs global-divisor-sum tension the corpus already names as the live frontier. **(L1)-(L4) do
not close it; they say where the constant lives and that it is stable.**

## 4. Standing caveats

* **Finite depth never confirms survival.** `ProgrammeSpine.md` section 12 (K1) proves survival is
  never implied by an open condition on `y`, so no enclosure engine can certify DRMH by
  running deeper. Depth here buys the *shape* of `H`, not the theorem.
* `Q_N / U(N) ~ 1/2` is measured at RECORDS only. It is not claimed off the records.
* (L3)'s ratio oscillates in `[0.2619, 0.2917]` with no trend. A constant-ratio reading and a
  monotone-drift reading are BOTH unsupported; only boundedness in the measured range is.
* (L1) is "divisor-rich", NOT "highly composite" — 25 of the 42 record successors do not set a
  `tau` record. Keying an argument to the HCN ladder keys it to the wrong set.
* The engine's certification is per-rank take/skip and aliveness, with an empty `undecided`
  list. That certifies the ORBIT to depth `4 x 10^6`; it says nothing beyond it.

## 5. Reproduce

```
./repo-python -c "
import sys; sys.path.insert(0,'.')
from system.lib.erdos257_lambda_greedy import greedy_lambda
import numpy as np
r = greedy_lambda(1, 21, 4_000_000, J=160, tau_max=1<<16)
Q = r['carry'].astype(np.int64)
H = np.maximum(np.maximum.accumulate(np.concatenate([[1], Q[:-1]+1])), 1)
d = np.arange(1, (len(H)-1)//2 + 1)
print('violations', int((H[2*d] > 2*H[d]).sum()), 'min slack', int((2*H[d]-H[2*d]).min()))
"
```
