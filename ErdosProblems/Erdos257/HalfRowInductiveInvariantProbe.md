# Half-row bank-hole congruence probe

## Claim boundary

This is a negative structural result, not a solution of Erdős 257 and not a
promotion of finite survival to an all-depth claim.  It tests exact
congruence lemmas that could have excluded the target-zero half-row bank
hole.  Three such lemmas are false.

For the even quotient row at endpoint `2d`, let `C_d` be the integer
residual immediately before the midpoint rank `d`.  The existing half-row
analysis singles out `C_d = 2^d` as the exact low-bank hole.  If the selected
proper ranks are `D_d`, then

\[
 C_d=2^{2d-1}-\sum_{a\in D_d}
       \left\lfloor\frac{2^{2d}}{2^a-1}\right\rfloor .
\]

The geometric quotient identity gives an exact low-half load

\[
 L_d=\sum_{a\in D_d}
      \left(\left\lfloor\frac{2^{2d}}{2^a-1}\right\rfloor\bmod 2^d\right),
 \qquad C_d\equiv-L_d\pmod {2^d}.
\]

Thus a nonzero residue would exclude the hole.  The script tests three
natural ways to force that nonzero residue and checks whether the full
modulo-`2^d` condition is genuinely weaker than the hole exclusion.

## Exact falsifiers

The dependency-free integer replay through `d = 2500` finds:

- The selected proper-divisor pulse need not be odd.  At `d = 14` it is
  exactly `2`, with `C_14 = 16776`.
- The low-half load need not stay below one modulus.  At `d = 11`,
  `L_11 = 3833 > 2^11`, with `C_11 = 263`.  A one-carry argument is therefore
  false.
- No fixed fourteen-bit nonzero window can work.  At `d = 575`, the exact
  pre-residual has two-adic valuation `15`, so it vanishes modulo `2^15`.

## Exact modular route obstruction

The partition identity gives

\[
 (L_d+C_d)\bmod 2^d=0.
\]

On the strict bank interval `0 < C_d < 2^(d+1)`, this implies

\[
 L_d\bmod 2^d=0\quad\Longleftrightarrow\quad C_d=2^d.
\]

Therefore a proof that the full low residue is nonzero would be the midpoint
hole exclusion itself, not an independent carry invariant.  The audit checks
the partition identity, strict bank boundary, and this equivalence at every
tested row.  Their finite success does not establish the all-depth bank
boundary or exclude a later hole.

## Non-duplication check

At `d = 26`, the probe obtains

\[
 C_{26}=102655489,
 \qquad C_{26}-(2^{26}+1)=35546624,
\]

with support `{2,3,6,7,14,20,21,26}`.  This is exactly the fixture of
`scripts/check_suffix_cylinder_orbit.py`.  Hence the underlying paired
endpoint recurrence is the already-known suffix-cylinder state, not a new
producer.  The durable delta here is the exact elimination of the three
congruence mechanisms above and retirement of full modular nonvanishing as
a merely renamed hole-exclusion route.

## Stop condition

Do not extend this scan merely to enlarge the horizon.  Re-enter only with
a source-coupled invariant that excludes `C_d = 2^d` without assuming an
equivalent modular nonvanishing statement, or with a proposed bounded window
whose universal statement can be killed by one exact state.

## Reproduction

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/scripts/half_row_inductive_invariant_probe.py --max-d 2500
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/scripts/half_row_inductive_invariant_probe.py --max-d 2500 --check-receipt state/formal_math/erdos257_period_noncollapse/half_row_inductive_invariant_probe_receipt.json
```
