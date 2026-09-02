# Erdős #1041: exact failure of universal centroid visibility

Status: exact rational counterexample to one proof mechanism, 2026-08-24.
The simplified small-rational certificate passed the exact canonical Lean
build on 2026-08-24.  This does not refute Erdős #1041.

## Statement

Let

```text
u(s)=((1-s^2)/(1+s^2), 2s/(1+s^2))
```

and take the five rational parameters

```text
0,
5/8,
7/2,
-11/3,
-5/7.
```

Set `r=99999/100000`, `a_j=r u(s_j)`,
`h=(a_0+...+a_4)/5`, and `f(z)=product_j(z-a_j)`.  Then all five roots are
distinct and have modulus `r<1`.  Every squared pair distance is greater than
the stronger close-pair certificate `5/9`; in fact the minimum is the pair
`(a_2,a_3)` and is approximately
`1.07341830`.

Nevertheless four of the five centroid spokes leave the unit lemniscate.  At
the following rational parameters on `[h,a_j]`, exact arithmetic gives

| spoke `j` | `t` in `h+t(a_j-h)` | `|f|^2` |
|---:|---:|---:|
| 1 | `23/100` | `1.0016393275...` |
| 2 | `1/4` | `1.0190022845...` |
| 3 | `1/8` | `1.0023556933...` |
| 4 | `3/10` | `1.0007936481...` |

Each displayed value is, exactly, greater than `1+1/5000`.  Hence at most one
root is visible from the centroid by a contained straight spoke.  In
particular there cannot be two centroid spokes forming an admissible broken
line, even though the configuration lies strictly inside the disk and remains
well inside the separated branch of the strengthened quintic close-pair
theorem.

## How the computation became a proof

The search began from the adaptive-MEC witness already present in the corpus.
At radius `9999/10000` a numerical probe found two safe centroid spokes, the
second with maximum about `0.999651`.  Scaling every direction by `r` also
scales the centroid by `r`, every spoke point by `r`, and a monic quintic value
by `r^5`.  This predicted that moving the directions closer to the unit circle
would cross the visibility threshold.  A bounded rational simplification then
replaced all four large parameters by `5/8, 7/2, -11/3, -5/7` while preserving
the stronger separation and four strict escapes.  The smaller certificate is
mathematically identical in force and substantially cheaper to check.

The four rational waypoints above then remove all floating-point dependence.
`scripts/check_erdos1041_centroid_hub_counterexample.py` constructs the
Gaussian rationals with `Fraction`, evaluates the factored polynomial, and
compares integer numerators.  `CentroidHubCounterexample.lean` independently
evaluates the same four rational inequalities with Lean's native decision
procedure.  The numerical search selected the certificate; it is not proof
authority.

## What survives

`CentroidHubBudget.md` remains valid: in every degree the centroid itself lies
strictly inside `{|f|<1}` and lies in the open major-axis-two ellipse of some
root pair.  This counterexample shows that those two automatic facts do not
force straight visibility.  It also sharpens the warning from the forum's Mac
Lane discussion: even a canonical interior hub with the exact metric budget
does not turn component geometry into short radial paths.

The surviving separated-quintic route must therefore allow a non-centroid
free hub, a critical hub, or a curved/component construction.  The present
polynomial may still have such a path; no negative statement about Erdős
#1041 is made.

## Exact handoff

Retire the universal two-spoke centroid conjecture.  Keep the all-degree
centroid interior/ellipse theorem as a metric basepoint lemma, but do not spend
further search on proving centroid visibility without additional hypotheses.
The next proof probe should compare a movable hub along the segment from the
centroid to a critical point against the already-measured free-hub optimum.
