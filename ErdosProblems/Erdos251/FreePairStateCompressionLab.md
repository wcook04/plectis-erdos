# Erdős 251: the shift is free, the ±2 wall is redundant, and the denominator is bounded below

## Claim boundary

Erdős #251 remains **open**. Nothing here proves cofinality. What is established:
three proved reductions that strictly weaken the recorded obligation, one finite
denominator exclusion where the packet recorded none, and a certified
computational verification of the weakened producer out to 1.27 million primes.
The remaining input is still a statement about prime gaps that is not a theorem.

## Setup

`g_i = p_{i+1} − p_i` (zero-based, `p_0 = 2`), `S = Σ_{i≥0} g_i 2^{−(i+1)}`, and

```
T_N = 2^{N+1}( S − Σ_{i≤N} g_i 2^{−(i+1)} ) = Σ_{k≥1} g_{N+k} 2^{−k},
T_{N+1} = 2 T_N − g_{N+1}.
```

## 1. The shift is free, not fixed

Suppose `S = a/b`, `b = 2^σ d` with `d` odd, and put `t = ord_d(2)`. For `N ≥ σ`,
`T_N = 2^{N+1}S − I_N` with `I_N = Σ_{i≤N} g_i 2^{N−i} ∈ ℤ`, so

```
T_M − T_N = 2^{N+1}(2^{M−N} − 1)·a/(2^σ d) − (I_M − I_N).
```

For `N+1 ≥ σ` the dyadic part clears, and `d | 2^{M−N} − 1` exactly when
`t | M − N`. Hence

> **(F)** `T_M − T_N ∈ ℤ` for **every** pair with `M ≡ N (mod t)`.

The recorded producer `cofinal_adjacent_small_mismatch` fixes an offset `h` and
asks for the property at `(N, N+h)` **for each `h ≥ 1`**. (F) says the two
indices need only be congruent mod `t`, with `M − N` an arbitrary multiple.
Since the fixed-offset form is the special case `M = N + h`, the free-pair
obligation is **strictly weaker**: one pair per cutoff, at unbounded distance.

That matters for the shape of the input. At a fixed offset the tail condition is
a *correlation* between two windows a bounded distance apart — which is where
Hardy–Littlewood enters. With `M` free it is a *hitting* condition on an
essentially unconstrained parameter.

## 2. The ±2 wall is redundant

The packet's `actual_prime_adjacent_mismatch_event_density` reduces the producer
to a single event: `Δ = +2` with `D = T_{N+h} − T_N ∈ (1/2, 1)`, or `Δ = −2`
with `D ∈ (−1, −1/2)`.

**Its first component alone is already a contradiction.** By (F), `D` is an
integer whenever `t | h`; an integer cannot lie in `(1/2, 1)`. The gap condition
`Δ = ±2` does no work.

The wall was an artefact of the consumer's window. `small_adjacent_shift_consumer`
requires two shifts in `(−1, 1)` — an interval that **contains** the integer 0,
so a second condition is needed to exclude `D = 0`, and that second condition
forces `|Δ| = |2D − (2D − Δ)| < 2|D| + 1 < 3`, hence `|Δ| = 2`. Choose instead
any interval free of integers and one condition suffices. So:

> **(P)** For every `t ≥ 1` and every cutoff, there are `M ≡ N (mod t)` beyond
> the cutoff with the fractional part of `T_M − T_N` bounded away from `0`.

That is the whole remaining content of Erdős #251 on this route. It is a
restatement rather than progress in itself — (P) is equivalent to irrationality —
but it is the sharpest form, and it shows the two-condition event was strictly
stronger than necessary.

**Lean.** `FreePairReduction.lean` lands (F) with its converse and the
equivalence. `free_pair_integral_iff_modEq`: at and beyond an odd-denominator
state with reduced denominator `d`, `T_M − T_N ∈ ℤ ⟺ M ≡ N (mod ord_d(2))`;
`exists_free_pair_lattice` packages the cutoff and the positive modulus for
every rational-valued orbit. (P) is `CofinalFreePairNonintegral`, with
"bounded away from `0`" read as non-integrality of the pair difference, and
`irrational_primeGap_tsum_iff_cofinalFreePairNonintegral` proves
`Irrational (Σ g_n/2^{n+1}) ⟺ (P)` for the real tail orbit `primeGapRealTail`
of the actual prime gaps. The fixed-offset criterion and (P) are equivalent
through irrationality (`cofinalFreePairNonintegral_iff_cofinalNonintegralTailShifts`).

## 3. State compression

Exchanging the order of summation with `m = N + k`,

```
Σ_{N≤X} T_N = Σ_{m≤X} g_m (1 − 2^{−m}) + Σ_{m>X} g_m (2·2^{−(m−X)} − 2^{−m})
            ≤ (p_{X+1} − p_0) + 2 T_X.
```

The `2 T_X` term is `O(max gap)` and so `o(X)`. **The bound without it is false**,
and falsifier 3 of the probe caught exactly that when this note was drafted with
the naive `Σ T_N ≤ p_{X+1}`.

Markov then gives, for any `C > 1`, a set `B ⊆ (X, 2X]` of density `≥ 1 − 1/C`
on which `T_N ≤ C log p_{2X}`. Under rationality every `T_N` lies in `(1/d)ℤ`,
so on `B` it takes at most `d·C·log p_{2X} + 1` distinct values. Hence

> **(SC)** some single value `v` has `#{ N ∈ (X,2X] : T_N = v } ≫_{d,C} X / log X`.

Rationality confines the **fractional parts** of the tails to an eventually
periodic orbit of multiplication by 2 modulo 1. Real tail *values* need not
be finite-state: the polynomial countermodel orbit `U_N = 2(N+4)^2` is
injective and integral. Markov still produces a near-linear set sharing one
lattice value of `T` on `(X,2X]`. Two consequences:

- Pairs with integral difference (and, on that Markov subset, often equal
  lattice values) are abundant for free. So the difficulty in (P) is entirely
  in producing a **non**-integral difference, never in producing a small one —
  the tail condition is not the obstruction.
- Splitting that set by `g_{N+1}, …, g_{N+L}` (at most `2^i v` choices at step
  `i`, since `T_{N+i} ≥ 2` forces `g_{N+i} ≤ 2^i v`) yields a gap word of length
  `L ≈ 1.7 √(log X)` repeating in `(X, 2X]`. That is **not** a contradiction —
  the birthday threshold is `L ≈ log X / log log X`, comfortably longer — and the
  gap is recorded here so the route is not re-walked.

## 4. First finite denominator exclusion

The packet records that it "contained no continued-fraction content" and no
finite denominator exclusion. One is cheap, because `T_N` is a **tail**: `P`
further gaps pin it exactly, with

```
T_{n₀} = U/2^P + T_{n₀+P}/2^P ,      U = Σ_{k≤P} g_{n₀+k} 2^{P−k}.
```

If `d·T_{n₀} ∈ ℤ` then `dist(dU mod 2^P) ≤ d·Θ` for any rigorous upper bound `Θ`
on `T_{n₀+P}`. Taking `Θ` from the **Lean-checked** elementary estimate
`p_n ≤ 1250(n+1)^4` — no gap conjecture enters — and using the
best-approximation theorem (the minimum of `dist(d U mod 2^P)` over `d ≤ D` is
attained at a convergent denominator of `U/2^P`), the certificate is complete
rather than a spot-check.

**Result at 4096 tail bits, index 1,266,144 of 1,270,606:**

> every odd `d ≤ ≈ 10^602` (2003 bits) is refuted, hence any rational `S = a/b`
> has `b > 10^602`.

Verified at **every** convergent denominator below the bound, not at a few
convenient small `d`. An earlier draft reported a bound exceeding `2^P`, which is
impossible; the sanity check now fails closed on that.

## 5. What the computation says about (P)

For `t ≤ 20` and **every** residue class mod `t`, over the last 10% of the
primes below `2·10^7`:

| | |
|---|---|
| primes | 1,270,607 |
| late window | indices 1,143,545 – 1,270,540 |
| leanest residue class at `t = 20` | **90,150** witnesses |
| latest witness index | **1,270,520** of 1,270,540 |
| sample at `t = 20` | `N = 1,270,520` (gap 10), `M = 1,222,260` (gap 12) |

Every recorded witness satisfies the **stronger** two-condition event
(`Δ = +2` and `D ∈ (1/2,1)`), so it certifies both the recorded producer and the
weakened (P) simultaneously. Witnesses run to the last usable index in every
class: cofinality is not marginal here, it is the generic behaviour.

## 6. The residual, sharpened

The route no longer needs Hardy–Littlewood correlation at a fixed offset. It
needs, for each `t`:

> cofinally many pairs `M ≡ N (mod t)` whose certified tail difference is
> non-integral.

Certifying one pair costs `O(log N)` gaps plus the elementary prime bound, so
each `(t, cutoff)` instance is a finite computation — §5 discharges every
instance with `t ≤ 20` in the window tested. What is missing is uniformity in
`t` and in the cutoff. The narrowest sufficient prime-theoretic input for the
two-condition form is **two Polignac numbers differing by 2, both occurring
infinitely often within a common index residue class mod `t`** — strictly less
than k-tuple correlation, and adjacent to bounded-gap technology rather than to
the Hardy–Littlewood conjecture. Whether it follows from known results is the
precise open sub-question this lab leaves.

## Replay

```sh
./repo-python formal_math/probes/erdos251_free_pair_and_state_compression.py
./repo-python formal_math/probes/erdos251_free_pair_and_state_compression.py \
    --limit 20000000 --max-t 20 --precision-bits 4096 --json
```

Four falsifiers: free-pair cofinality in every residue class with the latest
witness within slack of the last usable index; the ±2 wall on every recorded
witness; the averaging input `Σ T_N ≤ p_{X+1} + 2T_X`; and the denominator
exclusion verified at every convergent denominator, with a sanity check that the
bound cannot exceed `2^P`. Exit `0` iff all four pass. Receipt:
`state/formal_math/erdos257_period_noncollapse/erdos251_free_pair_receipt.json`.

## Correction, 2026-09-06 (appended; nothing above is rewritten)

**§4 is superseded and must carry the marker.** The `10^602` exclusion narrated
in §4 is correct as written and is superseded by two later results, both of
which this lab predates:

- the kernel-decided floor `b ≥ 2^589 > 10^177` for every rational `a/b` equal
  to the prime series and to the prime-gap series, proved inside the Lean
  kernel by `decide +kernel` on `cert_10000`
  (`KernelDenominatorFloor.lean:309, :315, :323`; receipt
  `state/formal_math/probes/erdos251_kernel_denominator_certificate_receipt.json`,
  which records `floor_den_bits_ge: 589` and `floor_den_decimal_digits_ge: 177`);
- the certified continued-fraction exclusion `q ≥ 2^39997`, hence `q > 10^12040`
  (receipt `state/formal_math/probes/erdos251_certified_cf_receipt.json`).

`claim_frontier_v1.json` records the supersession as
`erdos251.first_finite_denominator_exclusion_10e602 → erdos251.certified_cf_denominator_exclusion_10e12041`,
and `longitudinal_truth_2026_09_01.md:96` says never publish `10^602`. §4 stays
as the readable derivation of the tail-bracket method; it is not the current
figure.

**Two exponents, read from the receipt.** The receipt records four numbers:
`denominator_lower_bound_power_of_two_exponent: 39997`,
`denominator_lower_bound_bit_length: 39998`,
`strict_decimal_power_lower_bound: 12040`,
`denominator_lower_bound_decimal_digits: 12041`. The certified statement uses
the first and the third: `q ≥ 2^39997` and `q > 10^12040`. Surfaces printing
`2^39998 > 10^12041` have read a bit length and a digit count as exponents.
Raising the printed exponent does not strengthen the proof.

**Scale of the supersession.** `2^39997 / 2^589 = 2^39408`, and
`39408 · log10(2) = 11862.99`, so the continued-fraction exclusion exceeds the
kernel floor by more than `10^11862`. Earlier wording of "roughly 11,400 orders
of magnitude" and of "10^12034 weaker" is replaced by that figure.

**Evidence class of §2, §3 and §6.** State compression (§3), the redundancy of
the ±2 wall under (F) (§2), and the sharpened Polignac-pair residual (§6) are
ordinary proofs narrated here. The 2026-09-06 audit desk read the derivations
and found them sound. They carry no Lean, no independent check, and no receipt
beyond the four falsifiers of the replay probe. The naive averaging form
`Σ T_N ≤ p_{X+1}` is false and falsifier 3 catches it; the correct form is
`Σ_{N≤X} T_N ≤ (p_{X+1} − p_0) + 2 T_X`.

**§6 did not propagate.** The Polignac-pair residual of §6 is the narrowest
sufficient prime-theoretic input recorded anywhere for the two-condition form,
and it is strictly weaker than the Hardy–Littlewood `k`-tuple input named in
`AdjacentMismatchDensityLab.md`, in the research packet's `claim_ceiling`, and
in both `.tex` notes' closing discussions. Those surfaces still name the older,
stronger input. A dated correction was appended to the density lab on the same
date; the packet, the claim ceiling and the private `.tex` are outside the
2026-09-06 desk's write set and are recorded in
`docs/strategy/staging/rapid_breakout/audit/patches/frontier_251.json`.
