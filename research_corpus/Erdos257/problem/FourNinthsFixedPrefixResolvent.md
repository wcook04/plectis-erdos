# The fixed-prefix resolvent is the existing hole coordinate

## Result boundary

This note corrects the original interpretation of the computation.  The
certified intervals were right, but the claim that they defined a new proof
object was wrong: exact factorization identifies the resolvent with the
existing hole-geometry `Psi - theta` coordinate.  Nothing here excludes the
seam, constructs an infinite support, or resolves Erdős 257.

Let `P` be the fixed support prefix at the start of a no-strip ride.  Freeze
that prefix and extend its paired correction stream hypothetically forever:

\[
 C_n^P=2(t_{n+1}-g_P(n+1))+(t_{n+2}-g_P(n+2)).
\]

Define the convergent fixed-prefix resolvent

\[
 \boxed{\displaystyle
   \sigma_n^P=-\sum_{j\ge0}\frac{C_{n+2j}^P}{4^{j+1}}.}
 \tag{1}
\]

It obeys

\[
 \sigma_{n+2}^P=4\sigma_n^P+C_n^P.                 \tag{2}
\]

During the actual no-strip ride the boundary offset obeys the identical
inhomogeneous recurrence `x_{n+2}=4x_n+C_n^P`.  Therefore

\[
 \boxed{x_{n+2}-\sigma_{n+2}^P
        =4(x_n-\sigma_n^P).}                       \tag{3}
\]

## Exact factorization

Pairing the two binary rows removes the apparent novelty.  Write

\[
 \theta_n=\{2^n(4/9)\}
\]

and, for a selected rank `d`, let `rho_d(n)` be the least positive residue of
`-n` modulo `d` (equal to `d` when `d|n`).  Then

\[
 \begin{aligned}
 \sum_{j\ge0}
 \frac{2g_P(n+2j+1)+g_P(n+2j+2)}{4^{j+1}}
 &=\sum_{r\ge1}\frac{g_P(n+r)}{2^r}\\
 &=\sum_{d\in P}\frac{2^{-\rho_d(n)}}{1-2^{-d}}
 =:\Psi_n^P,
 \end{aligned}
\]

while the identical pairing of target digits is

\[
 \sum_{j\ge0}
 \frac{2t_{n+2j+1}+t_{n+2j+2}}{4^{j+1}}
 =\theta_n.
\]

Therefore

\[
 \boxed{\sigma_n^P=\Psi_n^P-\theta_n.}             \tag{4}
\]

The hole-geometry decomposition is

\[
 u_n=\theta_n-\Psi_n^P+Q_n.
\]

At the cylinder boundary `Q_n=x_n`, so

\[
 \boxed{x_n-\sigma_n^P=u_n.}                       \tag{5}
\]

Thus (3) is exactly the already-known rescaled greedy recurrence for `u`, not
a distinct anti-concentration mechanism.  The producer now verifies the
finite paired identity term by term and records this cross-program binding.

## Certified record rides

The producer reconstructs the exact cylinder to each of three record ride
starts.  It recomputes every future load directly from the frozen selected
divisors, sums 96 terms of (1) with exact denominator `4^96`, and encloses the
remaining infinite tail by

\[
 \frac{3|P|+3}{3\,4^{96}}.
\]

The resulting intervals certify:

| start rank | ride | `x` | `x - sigma` | tail radius |
|---:|---:|---:|---:|---:|
| `293578` | `13` | `11` | `3.58478338132539457e-4` | `2.35e-53` |
| `2287936` | `13` | `2` | `3.22992120360184303e-3` | `1.82e-52` |
| `4662078` | `11` | `9` | `1.26544697199219069e-1` | `3.71e-52` |

In every case the nearest integer to the entire certified resolvent interval
is exactly the ride's starting boundary offset.  The residual sign is also
certified, not inferred from floating point.

For the worst stall, multiplying the initial residual by `4^13` gives
`24057.074...`; the final boundary offset is `24061`, with the difference
accounted for by the transported bounded resolvent.  The max-width and longest
served rides reproduce the same identity exactly.

## What the certified numbers mean

The three displayed values are certified values of the existing `u_n`
coordinate at the record ride starts.  A polynomial lower bound

\[
  |x_n-\sigma_n^P|\ge C n^{-B}.                    \tag{6}
\]

would still be sufficient to bound ride lengths, but it is precisely a lower
bound on `u` for the actual rational orbit.  The hole-geometry programme
already owns that question, and genericity of `u` points toward survival rather
than proving Erdős 257.  Rephrasing it as resolvent anti-concentration does not
make the theorem cheaper.

The durable gain is negative and organizational: the seam and hole programmes
now share an exact coordinate dictionary, so future agents must not count
`sigma`, `Psi-theta`, and `u` as three mechanisms.

## Re-entry

Do not pursue resolvent anti-concentration as a separate lane.  Re-enter only
if a genuinely new positivity-and-set-ness invariant constrains `u`; otherwise
rotate to a structurally distinct construction or obstruction.  The escaped
novelty error is durably captured by Task Ledger event
`wie_20260822T173225Z_47c56c0e`.

## Reproduction

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/four_ninths_fixed_prefix_resolvent.py
./repo-python formal_math/erdos257_period_noncollapse/scripts/four_ninths_fixed_prefix_resolvent.py --check-receipt state/formal_math/erdos257_period_noncollapse/four_ninths_fixed_prefix_resolvent_receipt.json
```
