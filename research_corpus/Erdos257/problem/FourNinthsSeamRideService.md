# The 4/9 seam obstruction is a bounded service prefix

## Claim boundary

This is an exact finite mechanism census and a one-way proof target.  It does
not prove a uniform service bound, exclude the midpoint seam at every depth,
construct the infinite support, or resolve Erdős 257.

The computation is deliberately not another survival-horizon audit.  It
decomposes every maximal no-strip ride of the existing exact `4/9` cylinder
according to the local inequality that either forces multiplicative escape or
identifies the precise remaining obstruction.

## Exact seam coordinate

At even rank `n`, after removing all common leading bits, write the endpoint
interval as

\[
  [A_n-K_n,A_n]
\]

with suffix width `L_n`.  Minimality means that it crosses the highest suffix
boundary `B_n=2^{L_n-1}`.  Put

\[
  x_n=A_n-B_n,
  \qquad 0\le x_n<K_n.
\]

The exact two-row update is

\[
 A_{n+2}=4A_n+C_n,
 \qquad
 C_n=2(t_{n+1}-g_{n+1})+(t_{n+2}-g_{n+2}),       \tag{1}
\]

where the two `g` terms are the proper-divisor loads of the already fixed
support.  Relative to the enlarged boundary `4B_n`, put

\[
  u_n=4x_n+C_n.                                    \tag{2}
\]

There is no common-prefix strip exactly when

\[
  0\le u_n<K_{n+2};
\]

on such a step the new boundary offset is therefore

\[
  \boxed{x_{n+2}=4x_n+C_n.}                        \tag{3}
\]

## Escape service

Call a no-strip step *served* when

\[
  x_{n+2}\ge \max(1,2x_n).                         \tag{4}
\]

For positive `x_n`, this is just `C_n >= -2x_n`.  The `1` in (4) is
essential: it prevents the formal doubling condition from treating
`0 -> 0` as growth.

Once every remaining step of a ride is served, the positive offset doubles
until it leaves the corridor `x<K`.  Because `K_n` is linear, that tail has
length `O(log n)`.  Thus the difficult part of a ride is not its entire
length: it is the prefix through the last failure of (4).

The exact run through rank `10,000,000`, with an independent full-prefix
cross-check through rank `300`, contains `792,514` maximal no-strip rides.
It finds:

- maximum ride length: `13`;
- maximum escape-service stall prefix: `7`;
- maximum final served tail: `10` steps;
- maximum width immediately after a genuine strip: `23`.

The length-13 ride ending at rank `293,604` is also the unique displayed
worst service witness.  Its offsets are

```text
11,2,4,6,3,5,6,10,31,98,383,1511,6018,24061
```

and its corrections are

```text
-42,-4,-10,-21,-7,-14,-14,-9,-26,-9,-21,-26,-11.
```

The last failure of (4) is transition seven (`6 -> 10`); the remaining six
transitions more than double.  Hence any claimed universal stall bound below
`7` is exactly false on the actual initial state.

The longest served tail has length `10`; its offsets are

```text
9,3,6,12,38,137,520,2074,8298,33181,132699,530769.
```

The first transition is the sole stall, after which all ten transitions are
served.  The receipt retains both correction words and their exact odd/even
divisor-load ancestry.

## Why strips are not the remaining difficulty

If a strip occurs then `u_n<0` or `u_n>=K_{n+2}`.  In the upper case, after
removing the common leading `1`, the interval is `[u_n-K_{n+2},u_n]`; here
`x_n<K_n` and the positive part of `C_n` is bounded, so `u_n=O(n)`.  In the
lower case its distances below the boundary are bounded by
`K_{n+2}-u_n`, while `-u_n` is at most the divisor-load magnitude and hence
`O(n)`.  In either orientation, fully stripping the common prefix resets the
suffix width to `O(log n)`.

Consequently the following is a sufficient one-way theorem:

> Along the actual reachable `4/9` cylinder, the number of no-strip steps
> before permanent escape service (4) is uniformly bounded—or merely
> `o(n)`.

Together with the reset estimate, this gives `L_n=o(n)`, eventually keeps all
proper divisors inside the fixed prefix, runs the existing cylinder induction
forever, and produces an infinite Boolean support of exact value `4/9`.  That
support would disprove Erdős 257.

## Contrary evidence and proof discipline

A bounded service theorem cannot follow from arbitrary divisor loads or a
fixed finite prefix alone.  The existing CRT construction for ride words can
manufacture long local correction patterns when earlier reachability is
discarded.  A proof must therefore use the complete corridor history that
made the fixed support reachable.  The exact witness suggests focusing that
history on the first seven service failures rather than treating a 13-step
ride as an opaque anti-concentration event.

Do not extend the horizon without a proposed service lemma or falsifier.
Re-enter by tracing which reachable earlier decisions supply the large loads
in those stall steps, or by proving that a bounded number of such failures
exhausts a history-dependent resource.

## Reproduction

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/four_ninths_seam_ride_service.py --horizon 10000000 --crosscheck 300
./repo-python formal_math/erdos257_period_noncollapse/scripts/four_ninths_seam_ride_service.py --horizon 10000000 --crosscheck 300 --check-receipt state/formal_math/erdos257_period_noncollapse/four_ninths_seam_ride_service_receipt.json
```
