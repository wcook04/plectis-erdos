# Erdős 257: the exact margin law, and the closure of the divisor-multiplicity route

Status labels are strict. **[PROVED]** = elementary derivation given here.
**[COMPUTED]** = exact or certified-precision computation, reproducible from the
named script. **[HEURISTIC]** = model-based, not a theorem.

Erdős 257 (as stated in `ErdosProblems/Erdos257/HalfCounterexampleFrontier.lean`):
for every infinite `A ⊆ ℕ`, `Σ_{k∈A} 1/(2^k − 1)` is irrational. A counterexample
is an infinite `A` whose subsum is rational. `1/2`, `1/21`, `4/9`, `1/465` are the
corpus's candidate counterexamples: their greedy orbits survive to great depth.

Scripts: `scripts/cantor_staircase_run_length_lab.py`,
`scripts/divisor_multiplicity_periodicity_search.py`.
Both use a certified fixed-point engine (`M = 2·depth + 128` bits, explicit
interval bounds on every comparison; any undecidable comparison aborts the run
rather than guessing — `1/3 = w_2` correctly aborts as an exact tie).

## 1. The margin law [COMPUTED — exact to the bit]

Let `b = b_1 b_2 …` be the greedy support word of `y` and define the **margin at
rank n** as the distance from `ρ_{n−1}` to the fatal window `(Tail_n, w_n)`:
`ρ_{n−1} − w_n` on a take, `Tail_n − ρ_{n−1}` on a skip. Let

    R_n := length of the maximal run of (1 − b_n) starting at position n+1.

Then, over the pooled ranks 20…2500 of `1/2, 1/21, 4/9, 1/465`:

| `R_n` | count | mean(log2 margin + n) | min | max |
|---|---|---|---|---|
| 0 | 4988 | 0.000 | 0 | 0 |
| 1 | 2451 | −1.000 | −2 | −1 |
| 2 | 1229 | −2.002 | −4 | −2 |
| 3 | 622 | −3.000 | −3 | −3 |
| 4…13 | 626 | −R_n exactly | −R_n | −R_n |

    log2(margin_n) = − n − R_n          (min = max for every R_n ≥ 3)

This is an identity, not a correlation. **The distance from `y` to death at rank
`n` is a function of the run structure of `y`'s own support word and of nothing
else.** No numerator, denominator, congruence, valuation or height enters.

*Consequence.* This is the mechanism behind the corpus's measured absence of any
local signal (`GapAvoidanceReductionAndEquidistribution.md` §3). The survival
margin is not merely uncorrelated with the arithmetic of `y` — it is a function
of a different object, the word, and the word is generic (§4). Every mechanism
family that looked for a bias in `q`, in carries, in ownership or in valuations
was looking in a coordinate the margin does not depend on.

*Reading in `A`.* `R_n ≈ L` after a skip means `(n, n+L] ⊆ A`; after a take it
means `(n, n+L] ∩ A = ∅`. Since the fatal window has width `G_n ≈ (2/3)·4^{−n}`,
**death at rank `n` requires `ρ_{n−1}` to be within `≈ 2^{−n}/6` of the window's
edge, i.e. requires the would-be word to carry a run of length `≳ n` starting at
`n+1`.** Long runs are necessary for death, not sufficient: whether a near-tie
falls inside or outside `(Tail_n, w_n)` is exactly the sign of the margin, which
the run length does not see. So the run-length picture converts the *scale* of
the certification problem — `2^{−n−R_n}` against `4^{−n}` — into combinatorics of
one binary word, but does not by itself decide any orbit.

## 2. The divisor-multiplicity route is closed [COMPUTED — one-way]

Exact identity, from `1/(2^k−1) = Σ_{j≥1} 2^{−jk}`:

    Σ_{k∈A} 1/(2^k − 1) = Σ_{m≥1} τ_A(m) · 2^{−m},     τ_A(m) := #{d ∈ A : d | m}.

So the Erdős-257 value is the binary number whose (unbounded) digits are the
divisor multiplicities of `A`. This gives an obvious constructive attack:

> if `τ_A` is eventually periodic and bounded, the value is **rational**.

Since `τ_A = 1 * 1_A`, we have `1_A = μ * τ_A`, so the attack is exactly: find a
bounded eventually periodic `f ≥ 0` whose Möbius transform `μ * f` is a 0/1
indicator with infinite support. `divisor_multiplicity_periodicity_search.py`
runs this to exhaustion by DFS over `m = 1,2,3,…` (at each `m` the residue
`m mod r` is either fixed — verify — or free, with exactly two admissible values).

**Result.** For every period `r ≤ 24` and digit bound `≤ 6`, verified to `m ≤ 400`:
the solution count is exactly `2^{τ(r)}` and **every solution has `A ⊆ {d : d | r}`**.
(`r=12`: 64 = 2^6 solutions, `τ(12)=6`; `r=24`: 247 of 256, the 9 missing needing
a digit > 6; largest element of `A` equals `r` in every case.) So every solution
is finite, and the correspondence is `A ↦ f(m) = #{d ∈ A : d | gcd(m,r)}`.

    Any counterexample to Erdős 257 has APERIODIC divisor multiplicity τ_A.
    Its rationality is produced entirely by carry propagation, never by a
    periodic digit pattern.

This closes the natural forward-construction route, and is a different statement
from the corpus's existing period-noncollapse result: that one rules out
eventually periodic *support* `A`; this one rules out eventually periodic
*divisor multiplicity* `τ_A`, which is a strictly weaker hypothesis on `A` and
the one a constructor would actually reach for.

## 3. The carry coordinate [COMPUTED — exact, 0 violations]

Write `ε_m` for the (eventually periodic) binary digits of the rational `y`, and
`C_m := ⌊2^m · Σ_{j>m} τ_A(j) 2^{−j}⌋` for the carry into position `m`. Then

    τ_A(m) = ε_m + 2·C_{m−1} − C_m.

Verified with **zero violations** for `2 ≤ m < 1200` on `1/21`, `4/9`, `1/465`,
`1/2` (exact `Fraction` arithmetic; `C_m` computed from the exact tail
`y − Σ_{j≤m} τ_A(j)2^{−j}`, so no truncation enters).

**Corollary (free).** `ε` is eventually periodic for rational `y`. If `C` were
also eventually periodic then `τ_A = ε + 2·shift(C) − C` would be, and §2 makes
`A` finite. **So a counterexample needs an aperiodic carry sequence too.**

At depth 1200 the carries looked bounded and near-constant (`max C ∈ {7,…,10}`,
`C = 1` at `m = 400` and `m = 1200`), which suggested the automatic/Sturmian
regime. **Depth 9000 refutes that reading** — those were low-`τ` sample points,
not the trend (`scripts/carry_sequence_complexity.py`):

| target | alphabet | max C | mean C | entropy | eventual period (p ≤ 3000) |
|---|---|---|---|---|---|
| 1/2 | 16 symbols | 17 | 4.031 | 2.672 bits | none |
| 1/21 | 17 | 16 | 3.401 | 2.704 | none |
| 4/9 | 18 | 17 | 3.818 | 2.816 | none |
| 1/465 | 16 | 15 | 2.788 | 2.601 | none |
| 1/5 | 17 | 16 | 3.306 | 2.666 | none |

`C_m ≈ Σ_{k≥1} τ_A(m+k)2^{−k}`, whose mean is `Σ_{d∈A, d≤m} 1/d ≈ ½ ln m`
(`½ ln 9000 = 4.55`, matching the observed means). So `C` grows — slowly and
unboundedly — rather than settling. This is a new coordinate, and by §2 all of a
counterexample's structure must live in it.

## 4. Support words of rationals are generic [COMPUTED — negative]

Depth 6000, targets `1/2, 1/21, 4/9, 1/465, 1/5, 2/21, 4/21`:

* density `0.4935 … 0.5048`; max run 11–13 (`log2 6000 = 12.55`);
* subword complexity `p(11) = 1913 … 1951` of `2^11 = 2048`. The random-word
  prediction is `2048(1 − e^{−5990/2048}) = 1938`. Observed for `1/2`: **1939**;
* autocorrelation over lags `≤ 120`: `max |z| ≤ 3.74` (null expectation ≈ 2.8);
* **at lag `ord_q(2)` specifically**: `|z| ≤ 1.50` for every target;
* residue-class bias mod `ord_q(2)`: `χ² = 3.2 … 12.9`;
* correlation of `b_n` with `τ(n)`: `|z| ≤ 1.01`.

The support word of `p/q` carries no detectable trace of `q`. This extends the
corpus's equidistribution result from the skip-position statistic to the word.

## 5. Gap census and thickness [COMPUTED — exact]

    gaps ↔ odd dyadic rationals;  gap under σ_F (max F = n) has width G_n;
    Σ_{n≥1} 2^{n−1} G_n = E − 1 = 0.60669515…,   measure(𝒜) = 1 exactly,
    measure(𝒜)/E = 0.622396,
    Newhouse thickness τ(𝒜) = min_n Tail_n/G_n = Tail_1/G_1 = 1.542557 > 1.

Thickness `> 1` puts `𝒜` in Newhouse's regime, so `𝒜 + 𝒜` contains an interval
and `𝒜 ∩ (c − 𝒜) ≠ ∅` for an interval of `c`. That is a statement about pairs;
it does not produce a rational **in** `𝒜`, and is recorded as an invariant, not
an attack.

## 6. Engine validation

`A(4/21) = A(1/21) ∪ {3}` and `A(8/21) = A(1/21) ∪ {2}`, agreeing in 2999 of
3000 positions — forced, since `4/21 = 1/21 + w_3` and `8/21 = 1/21 + w_2` and
`2,3 ∉ A(1/21)`. `2/21` is unrelated (agreement 0.5013). `1/3 = w_2` aborts as an
exact tie rather than being silently decided. These are correctness checks on the
engine, not findings.

## 7. The carry sequence has full complexity [COMPUTED — closes the automatic route]

Aperiodicity (§3) plus a bounded alphabet would put `C` in the regime where the
Mahler–Nishioka and Adamczewski–Bugeaud transcendence theorems for automatic and
low-complexity sequences apply. They do not. Subword complexity of the deep tail
(`m ∈ [4500, 9000]`, so 4493 windows available):

| target | p(1) | p(2) | p(3) | p(4) | p(5) | p(6) | p(7) | p(8) |
|---|---|---|---|---|---|---|---|---|
| 1/2 | 16 | 92 | 390 | 1215 | 2578 | 3744 | 4272 | 4439 |
| 1/21 | 17 | 104 | 454 | 1449 | 2970 | 4050 | 4388 | **4475** |
| 4/9 | 17 | 112 | 471 | 1432 | 2934 | 3994 | 4363 | 4463 |
| 1/465 | 16 | 97 | 398 | 1202 | 2518 | 3681 | 4271 | 4435 |
| 1/5 | 17 | 102 | 426 | 1359 | 2813 | 3944 | 4355 | 4452 |

`p(8)` saturates the sample size (4475 of a possible 4493): essentially every
length-8 window of the carry sequence is distinct. The complexity is bounded by
how much data there is, not by any structure in `C`. **The carry sequence is
aperiodic and high-entropy, so no automatic-sequence transcendence theorem
reaches it.** That closes the lane §3 opened.

## 8. What this does not claim

* Nothing here proves or refutes Erdős 257.
* §1 does not give a survival certificate. A long run is necessary for death and
  not sufficient; the surviving/dying distinction at a near-tie is the sign of
  the margin, which is finer than the run length.
* §2 closes periodic `τ_A` only. Aperiodic `τ_A` with rational value is exactly
  what remains open, and is where §3 says the whole problem now sits.
* §5 is an invariant of `𝒜`, not a route.
* §7 closes the automatic/Sturmian lane for the carry sequence; it says nothing
  about aperiodic high-entropy `C`, which is what a counterexample must have.

## 9. The correct null for any "does arithmetic predict survival" claim

`scripts/denominator_survivor_census.py` decides survive/die **exhaustively** for
all 149,017 reduced `p/q` with `q ≤ 700` (global rate 0.50008). Binned by the
continued fraction of `y`, it reports enormous deviations — `|z|` up to **11.9**
across 84 cells where the null max is ≈ 2.98. That looks like the first
arithmetic fingerprint anyone has found on this problem. It is not.

Survival is overwhelmingly a function of **position**, because the rank-1 gap is
`(E−1, 1) = (0.6067, 1)`:

| `y ∈` | .0–.1 | .1–.2 | .2–.3 | .3–.4 | .4–.5 | .5–.6 | .6–.7 | .7–.8 | .8–.9 | .9–1 |
|---|---|---|---|---|---|---|---|---|---|---|
| survive | .9480 | .8602 | .6910 | .6261 | .8606 | .9478 | .0668 | **0** | **0** | **0** |

(`.6–.7` is `0.0668`; the surviving sliver is exactly `[0.6, E−1]`, width
`0.0067` of a `0.1` bin. Nothing above `E−1` survives at all.) The continued
fraction encodes magnitude directly through `a_1 = ⌊1/y⌋`, so **any** statistic
correlated with position inherits a huge spurious `z`.

`scripts/cf_signal_control.py` runs the Cochran–Mantel–Haenszel test under two
stratifications:

| control | strata | max &#124;z&#124; over 84 cells | null max |
|---|---|---|---|
| none (reproduces the census) | 1 | **11.945** | 2.98 |
| (a) `y`-value, 200 equal bins | 200 | **9.474** | 2.98 |
| (b) greedy prefix `b_1…b_8` | 136 | **3.048** | 2.98 |

Under (b) the signal is gone — `3.048` against a null max of `2.98` is textbook
noise. Note that (a) is *not* enough: uniform value-bins are too coarse, because
the survival rate swings violently inside any interval (the structure is Cantor,
not smooth). **The correct null is stratification by the greedy prefix**, which
conditions on the cylinder of `𝒜` that `y` occupies.

This is a methodological result, not a mathematical one, and it is the reason to
record it: an uncontrolled correlation study on this problem will manufacture
`|z| ≈ 12` out of nothing. Any past or future "mechanism" claim resting on a
survival correlation must be re-run under stratification (b) before it counts.

## 10. Where the problem actually sits now

Combining §1–§9: the margin is a function of the support word alone (§1); the
word is generic (§4); the carry sequence is aperiodic and high-entropy (§3, §7);
periodic `τ_A` is impossible (§2); and no arithmetic statistic survives the
correct null (§9). The height route is separately dead — `ρ_n` has denominator
`≈ 2^{0.3n²}` against a window of width `≈ (2/3)4^{−n}`.

What remains is one exact constraint system. Writing `ε` for the periodic digit
word of `y` and `C` for the carries:

    0 ≤ τ_A(m) = ε_m + 2C_{m−1} − C_m ≤ τ(m)      for every m,
    1_A = μ * τ_A  must be a 0/1 indicator with infinite support.

Two observations make this a genuinely different object from anything in the
corpus:

* **the carry recursion is local and contractive.** `C_{m−1} = ⌊(τ_A(m)+C_m)/2⌋`
  run downward halves its error each step, so `C_m` is pinned to within `2^{−L}`
  by `τ_A` on a window of length `L` above `m`. The carry structure is a sliding
  window — effectively a finite-state machine.
* **the divisor structure is global.** `τ_A(m) = Σ_{d|m} 1_A(d)` reads every
  divisor of `m`, at every scale.
* at a **prime** `p` the two meet: `τ_A(p) = 1_A(1) + 1_A(p) ≤ 2`, while the
  typical value of `τ_A(m)` is `≈ ½ ln m` (`≈ 4.5` at `m = 9000`). So the carry
  sequence is forced to dip hard at primes, and by Bertrand every dyadic block
  `(n, 2n]` contains one.

The open question is whether a local finite-state carry automaton can be made
compatible with a global divisor sum. That interaction is not a height argument,
not a congruence, and not a statistic, so nothing measured above rules it out.

## 11. The greedy is a bounded-look-ahead parity rule [COMPUTED — exact]

The carry identity of §3 is exactly **binary addition run from the least
significant end**, with `τ_A` as input digit stream, `C` as carry and `ε` as
output:

    ε_m     = (τ_A(m) + C_m) mod 2
    C_{m−1} = (τ_A(m) + C_m) div 2

Since `τ_A(m) = t_fixed(m) + 1_A(m)` where `t_fixed(m) = #{d ∈ A : d | m, d < m}`
reads only indices **below** `m`, the output bit **forces membership**:

    1_A(m) = ( ε_m + C_m + t_fixed(m) ) mod 2.

Verified **4000/4000** at depth 4000 on `1/2, 1/4, 3/8, 1/21, 4/9, 1/465, 1/5,
2/21, 5/12, 3/7` (`scripts/integer_carry_greedy.py`). And `C_m` is pinned by
`τ_A` on a short window above `m` — the downward recursion contracts by a factor
2 per step and `C ≤ 13` in range, so a seed of 32 and `L = 12` steps recovers the
exact carry **1500/1500** for every target.

So the Mersenne greedy — defined by real comparisons `ρ_{n−1} ≥ w_n` against
irrational tails — is equivalently a **parity rule with 12-step look-ahead on the
divisor lattice**, with no real numbers in it.

**Dyadic degeneracy.** For dyadic `y`, `ε_m = 0` past the last 1-bit, so
`τ_A(m) + C_m` is always even and the downward recursion admits a persistent
off-by-one: a seed *below* the true carry stays exactly one below forever. The
measured seed-below offset is `{−1}` for `1/2, 1/4, 3/8` and `{0}` for every
non-dyadic target, and the count of `m ≥ 2` with `τ_A(m)+C_m` odd is exactly the
number of 1-bits of `y` past position 1 (0, 1, 2 for `1/2, 1/4, 3/8`; 2000/5999
for `1/21`, whose period-6 word has two 1s; 3000/5999 for `4/9` and `1/5`). **The
corpus's flagship candidate `1/2` is precisely the degenerate case of the
transducer.** (The `1/2`-specific carry recursion itself is already in the corpus
as `HalfCarryReachability`; what is new here is the general-`y` transducer, the
bounded look-ahead, and the dyadic/non-dyadic dichotomy.)

**What this is not.** It is a local *characterisation*, not a forward algorithm:
deciding `1_A(m)` needs `C_m`, which needs `1_A` on `(m, m+12]`, so the recursion
regresses. The support is the unique sequence satisfying a 12-window parity
consistency relation over the divisor lattice — a subshift-like object rather
than an orbit. That is what makes it searchable and formalisable, and it is a
different handle from anything measured in §§1–10.

**Refuted en route.** The rule "take `m` into `A` whenever `C_m` stays `≥ 0`" is
*not* the Mersenne greedy: it agrees with the true support at chance level
(1974/4000 for `1/21`) and pins `C ≡ 0`. Recorded so it is not retried.

## 12. The carry peaks at primes [PROVED + COMPUTED]

**[PROVED]** For any target `y < 1`, the index `1` is never in `A` (`w_1 = 1`).
So at a prime `p` the only divisor of `p` that can lie in `A` is `p` itself:

    τ_A(p) = 1_A(p) ∈ {0,1}.

Substituting into the forward recursion `C_p = 2C_{p−1} + ε_p − τ_A(p)` gives, at
**every** prime,

    2 C_{p−1}  ≤  C_p + 1.

The carry is forced to at most half its running bound immediately before every
prime, and by Bertrand's postulate a prime lies in every `(n, 2n]`, so the
constraint fires at every dyadic scale. Dually, `C_m` is large exactly where
`τ_A(m)` is small, so the carry's maximum should sit at a prime.

**[COMPUTED]** Depth 8000, all nine surviving targets of
`1/2, 1/21, 4/9, 1/465, 1/5, 5/12, 3/7, 2/21, 3/8` (`7/15` dies):

| target | max C | max C_(p−1) | ⌊(maxC+1)/2⌋ | argmax C prime | mean C | mean C_(p−1) |
|---|---|---|---|---|---|---|
| 1/2 | 17 | 9 | 9 | yes | 3.969 | 2.837 |
| 1/21 | 16 | 8 | 8 | yes | 3.345 | 2.167 |
| 4/9 | 17 | 9 | 9 | yes | 3.757 | 2.701 |
| 1/465 | 15 | **7** | 8 | yes | 2.732 | 1.764 |
| 1/5 | 16 | 8 | 8 | yes | 3.248 | 2.151 |
| 5/12 | 16 | 8 | 8 | yes (both) | 3.709 | 2.310 |
| 3/7 | 16 | 8 | 8 | yes | 3.644 | 2.368 |
| 2/21 | 16 | 8 | 8 | yes | 3.478 | 2.368 |
| 3/8 | 17 | 9 | 9 | yes | 3.981 | 2.792 |

* **argmax `C` is a prime index for 9 of 9.** Prime density near `m = 8000` is
  `1/ln 8000 = 0.111`, so this is not chance (`0.111^9 ≈ 3·10^{−9}`). The carry is
  largest exactly where the divisor supply vanishes.
* the halving bound is **saturated for 8 of 9**; `1/465` falls one short. The
  inequality is a theorem and always holds — only its saturation is empirical.
* `mean C_(p−1) / mean C = 0.65…0.72` on every target.

**Why this is different from §§4, 9.** Those were searches for a *statistical*
signal, and both came back null under the correct control. This is not a
correlation: it is an identity-level constraint that is active and mostly
saturated. It is the first forced arithmetic structure in the carry coordinate.

**What it does not yet do.** It does not bound `C` — the observed growth
`max C ≈ ½ ln m` is compatible with the halving, because the carry is rebuilt from
composite supply between primes. Turning §12 into an obstruction would need the
supply between consecutive primes to be provably insufficient, which is a
statement about prime gaps against the divisor-density of `A`, and is untested.

## 13. Exhaustive deep-death hunt [COMPUTED — 10.9M rationals]

`scripts/exhaustive_deep_death_hunt.py`. **Every** reduced `p/q` with `q ≤ 6000`
— 10,943,163 rationals, 34× the corpus's largest run and exhaustive rather than
sampled — carried to depth 44 with certified fixed point (`M = 184` bits).

    alive at depth 44:  5,471,303 / 10,943,163  =  0.4999748

**[PROVED] that fraction is exactly 1/2.** `𝒜` is symmetric about `E/2` (complement
the support), and `(E−1, 1)` is the rank-1 gap, so `𝒜 ⊆ [0, E−1] ∪ [1, E]` with the
two pieces mirror images. `measure(𝒜) = 1` (§5), so each piece has measure `1/2`,
and `𝒜 ∩ (0,1) = 𝒜 ∩ (0, E−1]` has measure exactly `1/2`. A uniform random
`y ∈ (0,1)` survives with probability exactly `1/2`; the exhaustive rational count
agrees to `2.5·10^{−5}`.

**The failure law confirmed.** Against the corpus's
`P(fatal at n) = 0.25 · G_n/w_n`:

| rank | 5 | 6 | 8 | 12 |
|---|---|---|---|---|
| observed / predicted | 1.032 | 1.016 | 1.011 | 0.963 |

So the law holds to 1–4 % out to rank 12 on an exhaustive 10.9M-target census.

**The tail.** Deepest death rank observed: **19**. Deaths at rank ≥ 20: **zero**.
Expected count at ranks ≥ 20 under the fitted law is ≈ 3.5, so observing none is a
`e^{−3.5} = 0.030` event — mildly depleted, not significant. The tail is summable
as claimed; there is no enrichment of late deaths.

This is the strongest numerical evidence available that Erdős 257 is **false**:
about half of all rationals survive arbitrarily deep, and the failure process is
front-loaded with a summable tail. It also confirms the corpus's own finding that
the binding difficulty is certification, not discovery. (Note that my first null
here, a flat `2^{−(n+1)}`, was the wrong constant — the observed ratio settles at
0.34, and `0.25·G_n/w_n` is the correct law.)

## 14. Where the transcendence machinery stops [COMPUTED]

**Morse–Hedlund restatement.** `y = Σ_m τ_A(m)2^{−m}` has binary word
`ε_m = (τ_A(m)+C_m) mod 2`, determined by `A` alone (§11). And `y` is rational iff
`ε` is eventually periodic iff `p_ε(n) ≤ n` for some `n`. So:

    Erdős 257  ⟺  for every infinite A,  p_ε(n) ≥ n+1 for all n.

Any structured `A` whose `ε` drops to `p(n) ≤ n` is an outright counterexample.
`scripts/morse_hedlund_epsilon_complexity.py` scans thirteen families — lacunary
`2^k`, `k²`, `k³`, `k²+k+1`, primes, arithmetic progressions, Thue–Morse and
Rudin–Shapiro supports, Beatty `⌊kφ⌋`, squarefrees, Fibonacci, factorials. None
drops below the threshold, and none is eventually periodic within 400. But the
split is stark: `p(16) = 122` for lacunary `2^k` and `55` for factorials, against
`≈ 3800` (sample-saturated) for every positive-density family.

**The transition is sharp and it is at density ≈ 2^{−5}**
(`scripts/density_complexity_transition.py`, random `A ⊆ [2,12000]` of density δ,
`α = log₂(p(12)/p(6))`; `α = 1` is linear growth, `6` is full `2^n`):

| δ | 2^-10 | 2^-8 | 2^-7 | 2^-6 | **2^-5** | 2^-4 | 2^-3 | 2^-1 |
|---|---|---|---|---|---|---|---|---|
| α | 1.37 | 2.11 | 2.52 | 2.91 | **4.63** | 5.34 | 5.86 | 5.92 |
| p(12)/12 | 2.4 | 8.0 | 14.9 | 26.1 | **127.2** | 216.3 | 310.1 | 323.0 |

Below `δ ≈ 2^{−5}` the word `ε` has sub-exponential, near-linear complexity — the
regime the Mahler–Nishioka and Adamczewski–Bugeaud theorems operate in. Above it
`ε` saturates and no complexity-based theorem can reach it. The jump between
`2^{−6}` and `2^{−5}` is a factor 4.9 in `p(12)`, not a gradient.

**And every candidate counterexample sits at the far side.** §4 measured the
greedy support density of `1/2, 1/21, 4/9, 1/465, 1/5, 2/21, 4/21` at
`0.4935 … 0.5048`. So the rationals live at density `1/2`, a factor 16 above the
transition, as far from the tractable regime as the problem allows.

**Claim boundary.** The transition is measured; the link to the theorems is a
route, not a proof. "Sub-exponential complexity" is strictly weaker than the
hypotheses of Mahler–Nishioka or Adamczewski–Bugeaud, so nothing here proves
irrationality for sparse `A` — it locates where such a proof could begin, and
shows the counterexamples are not there.

## 15. Multiplicative correlations are null too [COMPUTED]

Every correlation study in this corpus, §4 included, tested **additive** structure:
autocorrelation at lag `l`, residue classes mod `ord_q(2)`, `τ(n)` bias. But the
problem does not live on an additive lattice — `τ_A(m) = Σ_{d|m} 1_A(d)` couples
`b_d` and `b_m` exactly when `d | m`, so the natural axis is multiplicative.
`scripts/multiplicative_support_correlation.py` measures `corr(b_n, b_{dn})` for
`d = 2 … 16` over six targets at depth 12000 (90 cells):

| | max &#124;z&#124; | mean &#124;z&#124; | #(&#124;z&#124;>2) | #(&#124;z&#124;>3) |
|---|---|---|---|---|
| targets | 3.144 | 0.824 | 8 | 1 |
| matched random words | 2.191 | 0.794 | 3 | 0 |
| 1/21 shifted by 7 | 1.449 | 0.528 | 0 | 0 |

Null max over 90 cells is `√(2 ln 90) = 3.00`; expected `#(|z|>2) = 4.1`. Observed
`3.144` and `8`. Indistinguishable from the matched random control. **The last
untested axis closes.** The support word carries no multiplicative signal either.

## 16. The exact Diophantine form, and why the sufficient condition is razor-thin

Unwinding §1: with `x := F(y)` (the support word read as a binary number), death at
rank `n` is `|{2^{n−1}x} − ½| < h_n`, `h_n ≈ (1/6)2^{−n}`, which is exactly

    y survives forever  ⟺  |x − a/2^n| ≥ (1/3)·4^{−n}  for every n and odd a.

A **dyadic** Diophantine condition at exponent 2, with the explicit constant `1/3`.

*Sufficient condition.* If `x` is badly approximable with `sup a_i = K`, then
`|x − p/q| > 1/((K+2)q²)` for all rationals, dyadic included, so the condition
holds when `1/(K+2) ≥ 1/3`, i.e. `K ≤ 1`. **Only noble numbers qualify** — `x`
with all partial quotients eventually 1, Hurwitz constant `1/√5 = 0.447 > 1/3`.
The sufficient condition sits at the very edge of the Lagrange spectrum, which is
why no soft argument reaches it.

*How far are the rationals?* `scripts/badly_approximable_certificate.py` computes
`x = F(y)` to 900 bits and runs its continued fraction (~520 terms):

| y | 1/2 | 1/21 | 4/9 | 1/465 | 1/5 | 5/12 | 2/21 |
|---|---|---|---|---|---|---|---|
| max `a_i` | 745 | 3394 | 2559 | 465 | 3782 | 4031 | 4386 |
| median `a_i` | 2 | 2 | 2 | 2 | 2 | 2 | 2 |

Median 2, maxima in the hundreds to thousands — textbook Gauss–Kuzmin. No rational
is remotely close to badly approximable, as measure theory demands.

## 17. Ranking the candidate counterexamples [COMPUTED]

`min_n (n − R_n)` is useless as a certifiability measure: `R_1 ≥ 0` caps it at 1,
and the minimum sits at `n = 1` for every target, so it only reads the first two
bits. The meaningful quantity is the deep-regime excursion

    E(y) = max_{n ≥ 8} ( R_n − log₂ n ),        smaller = safer,

how far the run lengths exceed their typical size where a proof would have to work.
Over all 10,290 surviving `p/q` with `q ≤ 260` (`scripts/best_candidate_counterexample.py`):
`min −1.322, mean 2.405, sd 1.830, max 16.385` at depth 400.

**The ranking is depth-stable.** Spearman `ρ = 0.7517` between depth 400 and depth
3000 across all 10,290 survivors, and every one of the depth-3000 top eight was
already inside the depth-400 top 100. It is a `max` statistic, so individual
targets move — `25/56` fell from rank 4 to 6888 on one late excursion — but the
aggregate ordering holds.

**The corpus's flagships rank badly.** At depth 3000, of 10,290:

| y | 4/9 | 1/2 | 1/21 | 1/5 | 5/12 |
|---|---|---|---|---|---|
| E(y) | 1.098 | 2.852 | 4.461 | 4.913 | 5.193 |
| rank | 1366 | 5606 | **8410** | 8862 | 9089 |

`1/21`, the most-worked candidate in this corpus, keeps less headroom than 82 % of
rationals with `q ≤ 260`. `4/9` is the only flagship in the safer tail. The safest
targets found are `15/188` (`E = −0.845`), `57/242`, `132/229`, `19/79`.

**Claim boundary.** Headroom is not provability — no current technique consumes it,
so a better `E(y)` does not make a proof easier today. This is the only quantitative
discriminator anyone has produced between candidate counterexamples, and what it
says is that the flagship selection was not made on this axis and does not sit well
on it.

## 18. Broad target funnel modulo exact tail equivalence [COMPUTED]

The original ranking counted rational targets, but the mathematical state is the
greedy remainder.  If two legal prefixes have the same exact remainder after rank
`N`, determinism gives the same complete support tail from rank `N+1` onward.  The
targets differ only by the finite signed Mersenne sum

    y - y' = sum_{k ≤ N} (b_k - b'_k)/(2^k - 1).

They are one future orbit, not two candidate mechanisms.  This matters especially
for `E`, which ignores the first seven ranks: finite prefix translations manufacture
many identical scores.

`scripts/best_candidate_counterexample.py` now enforces this quotient.  A future-word
fingerprint only proposes a collision; the script collapses it only after exact
`Fraction` equality of the two greedy remainders at rank 256.  Historical targets
are carried as ineligible controls, and the canonical receipt is
`state/formal_math/erdos257_period_noncollapse/rational_target_headroom_funnel_receipt.json`.

The exhaustive screen over every reduced `p/q` with `q ≤ 2000` found 608,246 alive,
608,282 dead, and 59 exact-boundary/precision cases among 1,216,587 targets at depth
400.  To obtain 512 distinct tail states, the selector had to inspect 766 ranked
targets and discard **254 exact finite-prefix equivalents**.  All 512 selected states
remained mutually distinct through the exact depth-10,000 replay.

The leading distinct states at depth 10,000 are:

| rank | target | `E(y)` | witness rank |
|---:|---:|---:|---:|
| 1 | `333/1669` | −1.247928 | 19 |
| 2 | `267/1678` | −1.129283 | 70 |
| 3 | `167/829` | −1.097703 | 8766 |
| 4 | `121/657` | −1.000000 | 64 |
| 5 | `254/1685` | −1.000000 | 32 |
| 6 | `238/1979` | −1.000000 | 16 |

`1/21` was not selected by the metric; as a control it has `E = 4.460841` with
witness rank 93.  The earlier leader `15/188` was selected but fell to
`E = 0.400552` at rank 3103.

**Claim boundary.**  This computation corrects the state space and reallocates
experiments; it does not make a finite survivor into a counterexample.  Its exact
content is the common-remainder quotient and the certified finite words.  Any
analytic continuation must act on a distinct tail state or on a property shared by
the quotient classes, not on another finite prefix translation.

## 19. Low-complexity rational-tail search and independent falsification [COMPUTED]

The headroom metric probes gap avoidance.  A different possible route is to find a
rational target whose greedy support tail is genuinely low-complexity or visibly
automatic, then attack that structure analytically.  The durable probe
`scripts/rational_target_structure_funnel.py` exhausts all reduced `p/q` with
`q ≤ 1000`, ranks the depth-400 alive words by `(p(8),p(10))`, quotients the same
exact common-remainder relation as §18, and replays 512 distinct tail states to
depth 10,000.  Its receipt is
`state/formal_math/erdos257_period_noncollapse/rational_target_structure_funnel_receipt.json`.

The screen classified 304,191 reduced targets: 152,081 alive, 152,069 dead, and
41 exact-boundary/precision cases.  Obtaining 512 distinct states required reading
739 ranked targets and discarding 227 exact prefix equivalents.

At depth 10,000 every selected word saturated `p(8)=256`.  The lowest `p(16)` was
9140, while the minimum among 512 predeclared matched Bernoulli words was 9132.
The best short-period mismatch also stayed inside the matched null.  Two exploratory
extremes initially looked worth a real falsification test:

- `250/631` had `p(12)=3653`, below the matched depth-10,000 null minimum;
- `127/346` had lag-44 `z=-4.317`, just beyond the matched-null maximum.

Neither survived a predeclared **independent continuation segment** from ranks
10,000 through 29,999.  For `250/631`, the fresh segment had `p(12)=4071`, inside
the matched-null range 4041…4083 (mean 4064.625).  For `127/346`, persistence of
the original correlation predicted `z≈-6.453`; the fresh segment gave `z=0.481`
with mismatch rate 0.498296.  Moreover the original lag scan tested 32,768 cells,
giving normal-approximation family-wise `p≈0.404` for an extreme at least as large.

**Mechanism decision.**  There is no robust low-subword-complexity, short-period,
or fixed-lag outlier in this exhaustive denominator family and distinct-tail
cohort.  The two apparent signals were ordinary selection spikes and are closed by
fresh data, not by a longer-horizon survival claim.  This does not prove that every
rational greedy tail is normal; it removes the concrete automatic/morphic outlier
route suggested by the broad rational search and redirects analysis toward
structure not visible in finite-word complexity or short additive lags.

## 18. Base 2 is the unique critical base [COMPUTED — exact]

Erdős 257 is the `b = 2` case of: for infinite `A`, is `Σ_{k∈A} 1/(b^k − 1)`
irrational? Mapping the `b`-dependence exactly
(`scripts/base_b_tractability_map.py`, exact `Fraction` census to 60 levels):

| b | E_b | total gap | measure(𝒜_b) | dim = log2/log b | survival rate in (0,E_b) |
|---|---|---|---|---|---|
| **2** | 1.60669515 | 0.60669515 | **1.00000000** | 1.00000 | **0.62367** |
| 3 | 0.68215350 | 0.68215350 | 0 | 0.63093 | 0.00000 |
| 4 | 0.42109769 | 0.42109769 | 0 | 0.50000 | 0.00000 |
| 6 | 0.23414913 | 0.23414913 | 0 | 0.38685 | 0.00000 |
| 12 | 0.09853375 | 0.09853375 | 0 | 0.27894 | 0.00000 |

(3000 random rationals per base, depth 40, exact arithmetic; `b = 5,7,8,9,10,11`
all 0.00000 likewise.)

**`b = 2` is the only base where the achievement set has positive measure.** For
every `b ≥ 3` the total gap equals `E_b` exactly, so `𝒜_b` is a measure-zero
Cantor set of dimension `log 2 / log b`: level `n` has `2^n` bridges of length
`Tail_n ≈ b^{−n}/(b−1)`, so survival to depth `n` has probability `(2/b)^n`,
geometric. At `b = 3` that is `(2/3)^40 = 1.4·10^{−7}`, hence the observed zero.
At `b = 2` it is `1^n` — the critical value — and the measured rational survival
rate `0.62367` matches `measure(𝒜)/E = 0.6223956` to `2·10^{−3}`.

**Consequence, and it is a one-way result about method.** Any argument for the
`b ≥ 3` cases that runs through measure or dimension — "the achievement set is
null, so nothing lands in it" — **cannot be transported to `b = 2`**, because
`measure(𝒜₂) = 1 > 0` exactly (§5). The problem is hard at exactly one base, and
it is hard there precisely because that is where the set is fattest. A technique
that generalises across `b` is therefore the wrong thing to look for.

*Bug corrected en route.* The survival invariant is `ρ_n ≤ Tail_n` and must be
checked after **every** step, not only after a skip. At `b = 2` the two are
equivalent (`E₂ = 1.607 > 1`, and taking preserves the invariant). At `b ≥ 3`,
`E_b < 1`: a target above `E_b` is trivially non-representable, the greedy takes
every coin forever with a positive residual, and a skip-only check never fires.
A first run of this script reported spurious survival rates of 0.33–0.91 for
`b ≥ 3` for exactly that reason.

## 20. Inter-prime carry repair: exact local laws fail; a linear-slope route remains [COMPUTED]

At a prime `p`, the divisor load in the carry recurrence has almost no room: it
only sees selected divisors among `1,p`.  This makes the prime spikes natural
places to ask whether the composite ranks before the next prime `q` forcibly
repair the carry.  `scripts/interprime_carry_repair_falsifier.py` tests this on
the quotient-distinct rational tails from §18 and writes canonical receipts at

    state/formal_math/erdos257_period_noncollapse/interprime_carry_repair_falsifier_receipt.json
    state/formal_math/erdos257_period_noncollapse/interprime_carry_repair_falsifier_receipt_512x10000.json.

The simplest exact laws are false.  On 128 targets through rank 30,000, covering
412,928 consecutive-prime intervals:

- `C_(q-1) ≤ C_p` first fails for `333/1669` on `409 < 419`, with carries
  `C_409=2`, `C_418=3`, `C_419=5`;
- `C_q ≤ C_p+1` already fails for the same target on `127 < 131`, with
  `C_127=2`, `C_130=2`, `C_131=4`;
- `C_q ≤ max(C_p,ceil(log₂q)+4)` fails on `20773 < 20789`, where the proposed
  bound is 19 but `C_20789=20`;
- the largest prime-endpoint jump is 23 (`363/599`, `28549 < 28559`), and the
  largest observed excess above `ceil(log₂m)` is 17 (`740/1529` at rank 27719).

The pre-prime repair inequality holds in 0.86594 of the tested intervals and its
longest observed failure run has length only two.  That frequency is not a
producer: even a bounded run of such failures does not control the next-prime
peaks, which can double the pre-prime carry.  The experiment therefore discards
the one-gap monotonicity route rather than treating a high finite success rate as
evidence of a proof.

A different inequality survives and has the right logical output.  Ask whether,
for every legal carry, there is a finite constant `K` such that consecutive
primes `p<q` satisfy

    C_q - C_p ≤ K(q-p),
    max_{p≤m≤q} C_m - max(C_p,C_q) ≤ K(q-p).

The breadth run (512 targets to 10,000; 619,520 intervals) needs observed `K=5`.
The depth run needs `K=6`: its worst endpoint slope is `11/2`, attained by
`223/1957` on the twin-prime gap `21557 < 21559`, while its worst within-gap
overshoot slope is `10/3`, attained by `121/657` on `26203 < 26209`.  Thus the
data do **not** support freezing a numerical constant at a shallow horizon.
They identify two obstruction geometries that a proof must absorb: endpoint
growth at tiny prime gaps and interior peaks at highly composite ranks.

**Why this is a genuine producer if proved.**  The first inequality telescopes
over the prime skeleton to `C_p = O(p)`; the second fills the intervals between
primes, giving `C_n = O(n)`.  This is tempered carry growth and therefore excludes
the expanding homogeneous mode.  The computation has not proved either bound or
even that one constant works forever.  Its one-way content is narrower: it kills
the exact one-gap repair laws and isolates a prime-skeleton Lipschitz theorem whose
conclusion would directly discharge the carry-growth obstruction.

### Twin-prime resolution of the short-gap obstruction

The depth-30,000 value `K=6` is not stable.  The exact follow-up
`scripts/twin_prime_carry_compensation.py` uses the first sixteen distinct-tail
leaders together with every earlier extreme target and reaches rank 200,000.
It tests 45,213 target/twin-prime intervals.  On a twin-prime pair `p,p+2`, two
applications of the recurrence give the exact identity

    C_(p+2)-C_p
      = 3C_p - 2τ_A(p+1)
        + 2ε_(p+1) + ε_(p+2) - τ_A(p+2).                 (20.1)

The receipt checks (20.1), both binary digits, and the integer recurrence with
zero violations.  The bounded last line of (20.1) separates the real variable:
short-gap growth is governed by the compensation deficit
`3C_p-2τ_A(p+1)`.

The observed endpoint constant rises to `K=8`.  The first failures of every
integer `K≤7` are recorded.  The worst jump is 16 for `40/1067` on
`129917 < 129919` (`C_p=8`, `τ_A(p+1)=5`, `C_(p+2)=24`).  The worst deficit is
16 for `121/657` on `197597 < 197599` (`C_p=8`, `τ_A(p+1)=4`, endpoint jump
15).  Across successive dyadic bands beginning at 64, the worst observed
slopes are

    1.5, 1, 1, 2, 2.5, 4, 3.5, 4.5, 5.5, 7, 8, 8.

More decisively, a pointwise positive divisor-supply law is false.  For
`9/953` on the same terminal twin-prime pair, `C_p=5` but `τ_A(p+1)=0`, and
the endpoint jump is 14.  Thus neither `τ_A(p+1)≥1` nor
`τ_A(p+1)≥α C_p` for any universal `α>0` can be the repair mechanism.

**Mechanism decision.**  Fixed constants `K≤7` and pointwise proportional
compensation at the middle composite are eliminated by exact witnesses.  A
larger or orbit-dependent Lipschitz constant is not disproved, but the band
profile gives no basis for freezing one.  Any continuation of the prime-skeleton
route must control an **aggregate compensation deficit** across intervals (or a
slowly growing envelope whose telescoped growth is still subexponential), rather
than demand repair inside every short gap.  This is a structural redirection,
not a claim that rank 200,000 decides the infinite problem.
