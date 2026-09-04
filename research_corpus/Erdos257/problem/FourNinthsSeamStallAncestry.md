# The worst 4/9 seam stall is paid for by fresh divisors

## Result boundary

This exact ancestry computation eliminates a small-cycle explanation for the
worst observed escape-service stall.  It does not bound fresh contributor
supply at all ranks, exclude the seam, construct an infinite support, or
resolve Erdős 257.

The service coordinate and criterion are those in
`FourNinthsSeamRideService.md`:

\[
 x_{n+2}=4x_n+C_n,
 \qquad
 x_{n+2}\ge\max(1,2x_n).
\]

The length-13 ride ending at rank `293,604` has seven transitions before its
permanent served tail.  Six of those seven transitions fail service.  The
producer replays the actual cylinder, reconstructs the selected fixed support,
and independently enumerates every selected proper divisor contributing to
both rows of each transition.

## Exact decision

Across the six failures:

- `88` distinct selected divisors contribute;
- only `7` divisors recur across two or more failures: `2,4,5,7,8,12,13`;
- every failure introduces at least `4` contributors absent from all earlier
  transitions in the stall prefix.

The first failure, `11 -> 2`, is driven by weighted load `42` and introduces
`39` distinct contributors.  Later failures still require new supply even
after small recurrent divisors are available.  For example, the final failure
`6 -> 10` uses the recurrent set `2,4,8,12,13` but also seven newly appearing
contributors:

```text
24,39,52,78,137,2143,5646
```

Thus a proof cannot treat the seven-step stall as iteration of a small finite
bad state.  The actual obstruction is the reachable prefix's ability to
supply many one-use divisors to consecutive rows.

The script also traces the largest escape deficit in the ten-million-rank
census.  At source rank `1,349,998`, the transition `18 -> 10` has correction
`-62` and deficit `26`; one odd-row contributor and sixty even-row
contributors supply the entire weighted load.  The even row is `1,350,000`,
so its highly composite anatomy is explicit rather than hidden inside a load
count.

## One-way next theorem

The sharpened sufficient route is now history-sensitive:

> Bound, by `o(n)`, the number of consecutive escape-service failures that a
> reachable cylinder prefix can pay for with newly appearing selected
> divisors.

A merely local divisor argument cannot do this: CRT can manufacture fresh
large divisors for arbitrary prescribed short blocks when earlier corridor
reachability is ignored.  The proof must charge each new contributor to the
earlier corridor event that selected it and show that reachable selection
history cannot finance a linear stall.  Any such sublinear fresh-load budget,
combined with the already proved escape tail and extraction reset estimates,
gives `L_n=o(n)` and runs the `4/9` cylinder forever.  That would construct an
infinite Boolean support of exact value `4/9` and disprove Erdős 257.

Do not search for a repeated correction cycle in this witness; the exact
ancestry eliminates that mechanism.  Re-enter through fixation-time charges,
selection-cost accounting, or a contrary reachable witness with a long stall
but bounded fresh supply.

## Reproduction

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/four_ninths_seam_stall_ancestry.py
./repo-python formal_math/erdos257_period_noncollapse/scripts/four_ninths_seam_stall_ancestry.py --check-receipt state/formal_math/erdos257_period_noncollapse/four_ninths_seam_stall_ancestry_receipt.json
```
