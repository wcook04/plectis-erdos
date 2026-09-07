# Erdős 1041: a rigorous compact off-face stationary block

## Status

In the ordered chart

```text
u=r s w,  v=s w,
```

the stationary GP3 residual is strictly positive on the closed four-variable
block

```text
0<=t<=1,
1/4<=r,s,w<=3/8.                                      (1)
```

This is the first rigorous positive-volume block in the compact off-face
interior.  It complements the exact collapsed-face collars and the exact
isosceles slices.  It does not cover the rest of the ordered cone, prove GP3,
or prove Erdős 1041.

## 1. Cancelled interval form

The checker evaluates the same cancelled stationary formula used in
`ThreeExteriorStationaryCollapsedFaceCollar.md`:

```text
S_stat = RAW
       + 1/2 sum_(i<j) rho_i rho_j (L_i+L_j)
       - 1/2 sum_i rho_i^2 (L_i+L_j)(L_i+L_k)/(L_j+L_k),
```

where `(rho_1,rho_2,rho_3)=(rsw,sw,w)`.  On (1), every primitive denominator
is strictly positive.  In particular `rho_i<1`, all comparator products are
less than one, and each kernel `L_i` is positive.

Every arithmetic operation is evaluated as a binary64 interval.  After the
hardware round-to-nearest result, the lower endpoint is moved one
representable number toward minus infinity and the upper endpoint one number
toward plus infinity with `math.nextafter`.  Thus each primitive interval
contains the exact real operation.  All partition endpoints are dyadic and
therefore exactly representable.  The checker also verifies the binary64
radix, mantissa, exponent range, round-to-nearest mode, and adjacent-number
semantics before accepting the certificate.

## 2. Partition and exact replay data

The first partition uses

```text
64 cells in t,
16 cells in each of r,s,w,
```

for `262144` coarse cells.  The natural interval extension is strictly
positive on `224994` of them.  The remaining `37150` cells are dependency-red
only: split each spatial direction once, keeping its `t` cell fixed.  All

```text
8*37150 = 297200
```

refined cells have strictly positive lower endpoints.  No cell remains red.
The weakest accepted lower endpoint is the exact binary64 number

```text
0x1.5054f4388ffffp-21 = 6.264668917579929e-7 > 0.       (2)
```

Hashing every accepted lower endpoint in deterministic traversal order as a
big-endian binary64 word gives

```text
5b11d1a225c48e8e825863b17483715f8fff7ad6b9a65fc81a00b410977357f5.
```

The cell union is exactly (1), so (2) proves the theorem.

## 3. Replay and boundary

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_stationary_compact_interior_block.py
```

The replay is exhaustive and contains no sampling or optimizer claim.  Its
scope is exactly the block (1).  The surviving stationary obligation is the
complement of this block and the previously proved face/isosceles regions;
a larger adaptive atlas or a global analytic inequality is still required.
