# Erdős 68: the frontier's targets are not equally hard, and nobody had ordered them

## Claim boundary

Logical relations between statements already recorded in the packet, plus one
finite illustration from `m ≤ 22000`. It proves nothing new about `S` and Erdős
#68 remains open. What it does is stop effort being spent on a strictly harder
statement than the conclusion requires.

## The problem with a flat producer list

`research_packet.json` carries fourteen open producers, each tagged
`priority: 1` or `2`. Priority is an effort ranking. It is not a logical one, and
the packet records no relation between the producers at all — the
`frontier_integrity` block classifies each as `equivalent_to_target`,
`target_deciding_but_stronger`, or `auxiliary`, but never says which of the
stronger routes implies which.

So two producers can sit side by side at the same priority while one is strictly
harder than the other **for the same conclusion**. That is what happened.

## The order

Write the unit-carry window `W_m = ((1+ε_m)/m, (2+ε_m)/m]`, so `A_{m−1} ∈ W_m`
exactly when `D_m = 0`. Write `Z_m` for the **zero branch**: `D_m = 0` together
with `A_m ≤ R_m`, where `R_m = m!·Σ_{n>m} 1/(n!−1)`.

```
        Z_m  ⊊  W_m                                  (strict containment)

  escape W cofinally   ⟺   Erdős #68                 (equivalent)
  escape Z cofinally   ⟹   Erdős #68                 (sufficient)
  escape W cofinally   ⟹   escape Z cofinally        (so W-escape is HARDER)
```

The middle line is the content of `RationalCylinderMarginLab.md`: rationality
forces `canonicalRemainder(m−1) = 0`, hence `canonicalDigit m = 0`, hence the
zero branch — at *every* large `m`. The rest of `W_m`, the maximal branch, is
consistent with nothing in particular and rules out nothing.

So **escaping the whole window is strictly more than the problem needs.** Unless
a route specifically wants the equivalence, it should aim at `Z`.

## How much strictly weaker, measured

Over `13 ≤ m ≤ 22000`:

| set | entries | where |
|---|---|---|
| `W` (unit carries) | **9** | 52, 591, 1030, 1407, 1438, 2164, 4258, 10991, 21236 |
| `Z` (zero branch) | **0** | — |

The widths explain it: `|W_m| ≈ 1/m` with `Σ 1/m` divergent, `|Z_m| = R_m/m =
O(m^{−2})` with `Σ R_m/m` convergent. A desk aimed at `W` is proving escape from
a set that is demonstrably entered nine times; a desk aimed at `Z` is proving
escape from one that never has been.

That is not evidence — the expected `Z` count over *all* `m` is only about `1/3`,
so zero is unremarkable, and `RationalCylinderMarginLab.md` says so. It is a
statement about which target a proof has to fight.

## Where the fleet's desks sit

| desk | target | strength |
|---|---|---|
| 01 | zero branch, via dynamics | sufficient |
| 02 | residue equidistribution → the sum's fractional part | routes to `W` |
| 03 | the integer certificate | sufficient — it excludes `Z` |
| 04 | lower cylinder at primes | sufficient, plus a prime restriction |
| 05 | `E`-function linear independence | independent route |
| 06 | finite `S₂` digit law plus infinite-floor stability | auxiliary until the floor comparison is proved cofinally |
| 07 | separating invariant | independent route |

**Desk 01 was aimed at `W` and has been retargeted to `Z`.** As stated it asked
for a strictly harder statement than desks 03 and 04, for the same conclusion,
with no compensating gain — its mechanism (shrinking-target dynamics) applies to
`Z` unchanged and rather better, since an `O(m^{−2})` target is exactly the
regime where Borel–Cantelli has room.

Desk 06 has been corrected. Lean now proves the finite identity
`d_m(P²_m)=m−1−b_m`. The earlier `m−2−c` statement used a backwards carry with
a finite terminal condition and also inferred floor equality from a subunit
tail. The target-facing version is: prove the infinite second-layer floors are
stable cofinally and then rule out `d_m(S₂)=m−2` eventually. Until that
floor-stability bridge is proved, desk 06 is auxiliary rather than an established
equivalence.

## What to take from this

Two things, neither of them about `S`.

A flat priority list hides logical structure. Fourteen producers were tracked for
months without anyone recording that one of them implies another; the relation
falls out of a single Lean proof once you read which branch rationality occupies.

And "equivalent to the target" is not automatically the best thing to attack. An
equivalence is worth having when it converts the problem; it is worth avoiding
when a strictly weaker sufficient statement is sitting next to it with a
convergent measure instead of a divergent one.

## Replay

The containment and the counts:

```sh
./repo-python formal_math/probes/erdos68_rational_cylinder_margin.py --max-m 22000
```
