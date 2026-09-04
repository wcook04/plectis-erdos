# The worst 4/9 stall spans all co-divisor scales

## Exact elimination

This computation eliminates a finite-small-quotient explanation for the worst
observed seam stall.  It does not prove an all-depth service bound, exclude the
seam, construct an infinite support, or resolve Erdős 257.

For a selected contributor `d | m`, write its co-divisor as `q=m/d`.  The odd
row has weight two and the even row weight one.  At a no-strip state with
offset `x`, the exact weighted load must exceed

\[
  4x+t-\max(1,2x)

\]

to fail escape service.  Sorting all weighted contributors by `q` therefore
gives an exact minimum quotient cutoff capable of financing each failure.

For the six failures in the length-13 ride, those cutoffs are

```text
630, 73396, 827, 146794, 8635, 73398.
```

Consequently:

- no failure is financed by the channels `q <= 50`;
- no failure is financed by `q <= 500`;
- only two of six are financed by `q <= 1000`;
- only three of six are financed by `q <= 10000`;
- one transition (`3 -> 5` at source rank `293586`) needs every one of its
  eight weighted contributors, reaching `q=146794`.

The final service failure (`6 -> 10`) is similarly broad: its smallest
co-divisor is already `52`, and thirteen of fourteen weighted contributors
are needed, reaching `q=73398`.

Thus the fresh-load obstruction cannot be reduced to a fixed automaton over a
small set of quotient diagonals.  Small divisors, large divisors, and their
paired co-divisors all matter on the same actual ride.

## Consequence for proof search

The remaining useful charge must be scale-uniform.  Plausible forms include a
weighted sum over all quotient channels, a fixation/extraction budget that
does not distinguish `d` from `m/d`, or a global positive resolvent.  A proof
that monitors only finitely many low quotients will miss a witnessed service
failure and cannot establish the `4/9` cylinder.

This negative result combines with the diagonal-charge audit: the stall is
neither a diagonal small-margin event nor a finite low-quotient pattern.  Its
remaining structure is genuinely the globally reachable, positive,
set-valued divisor transform.

## Reproduction

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/four_ninths_stall_codivisor_spectrum.py
./repo-python formal_math/erdos257_period_noncollapse/scripts/four_ninths_stall_codivisor_spectrum.py --check-receipt state/formal_math/erdos257_period_noncollapse/four_ninths_stall_codivisor_spectrum_receipt.json
```
