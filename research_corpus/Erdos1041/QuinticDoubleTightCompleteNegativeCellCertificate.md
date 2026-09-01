# Erdős 1041: complete five-sheet macroscopic negative cell

Date: 2026-08-30. Exact replay:
`scripts/check_erdos1041_quintic_double_tight_complete_negative_cell.py`.

## Result

On the common rational interval

```text
-13/12500 <= t <= -3/3125,
```

the checker isolates all five upper-half-plane roots of the unordered
critical-value carrier, identifies their ordered `(t,a,mu)` branches at
`t=-1/1000`, fixes every wall chamber, and applies exact positive-gradient
transport to both inverse-ray arms.

The exact transported upper endpoints are

```text
-0.031806457,
-0.911548111,
-1.063844718,
-1.265078597,
-1.024694817.
```

Thus every sheet satisfies `mathcal E<-1/100` throughout the interval.  The
five parameter tubes are pairwise disjoint and strictly upper-half-plane,
and all seventeen exact replay gates are green.  The degree-ten carrier
theorem supplies upper-sheet exhaustion, so the result covers the complete
physical fibre, not merely the weak branch.

This is a local complete-fibre theorem.  It does not alone cover the other
regular branch truncations or prove `EX-W`, `EX-U`, degree five, or
unrestricted Erdős 1041.
