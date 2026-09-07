# Erdős 1041: exact support-cone obstruction at the weighted cusp

Date: 2026-08-30. Exact replay:
`scripts/check_erdos1041_quintic_weighted_cusp_support_bridge.py`.
Consumes the square-root-free support engine and the weighted cusp carrier.

## Result

The current fixed-strip/support-Stieltjes schedule does **not** extend the
proved positive collar beyond `u=1/1000`.  This is an exact method boundary,
not evidence that the desired excess sign is false.

On the rational microcell

```text
1/1000 <= u <= 1001/1000000,
```

the checker isolates the three distinct upper `mu=-10` cusp sheets and runs
both compact arms with 1024 exact rational `r`-cells.  The two strong sheets
have support upper bounds approximately

```text
-0.4257397998,  -0.9639009374,
```

but the weak sheet has upper bound

```text
+0.5564295588.
```

More decisively, setting the parameter radius to zero at the exact endpoint
`u=1/1000` still gives

```text
support upper = +0.5498795714.
```

One compact arm has 461 turn-ambiguous cells paid by the direct nonnegative
fallback.  Since this positive loss remains on a zero-width parameter fibre,
further subdivision in `u` cannot repair this particular schedule.  A useful
successor would have to isolate the vertical turns/fixed-strip crossings or
replace the direct-cell payment; mere parameter refinement is ruled out.

## Exact boundary

The fully bit-replayable five-sheet positive theorem remains

```text
0 <= u <= 1/1000,
```

with weakest exact transported upper `-0.02354340` from
`QuinticWeightedCuspTransportToOneThousandth.md`.  No extension to `u=1/100`
or complete double-tight theorem is claimed here.  The failed WCT-2 gradient
draft is not consumed and is not promoted by this obstruction.
