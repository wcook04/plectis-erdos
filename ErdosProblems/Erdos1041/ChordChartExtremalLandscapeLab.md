# Erdős #1041: the chord-chart extremal landscape (lab note)

Status: measurement, 2026-09-05. **Nothing here is a theorem about Erdős
#1041.** Every number below is a finite floating-point search over finitely many
configurations, and the searches are reported with their basins per negative
result 28 of the kill-list. The exact statements this lab surrounds are proved in
[CentroidVarianceChordChart.md](CentroidVarianceChordChart.md), which is the
authority for anything universal.

The lab answers three questions in the root-statistic coordinate.

1. Where does `m(f)`, the intrinsic distance inside `{|f| < 1}` between the
   closest pair of roots in that metric, attain its largest values?
2. How large is the region with no contained straight root chord, and what are
   its statistics?
3. Does anything defeat both the chord chart and a two-spoke path from one of
   the canonical hubs `0`, the centroid, and the critical points?

## Method and its direction of error

`m(f) = min over distinct root pairs of inf{ length(gamma) : gamma joins them
inside {|f| < 1} }`. It is not directly computable, so every reported number is
a **verified upper bound**, obtained as follows.

* A grid Dijkstra over the square bounding box of the roots, 16-neighbour
  stencil (all `(dx,dy)` with `gcd(|dx|,|dy|) = 1`, `|dx|,|dy| <= 2`), on cells
  where `|f| < 1` at the cell centre, from every root to every other root.
* The resulting polyline is greedily shortcut: a sub-polyline is replaced by its
  chord whenever `max |f|` on that chord, sampled at 300 points, is below one.
* The final polyline is verified by resampling `max |f|` at 500 points per
  segment. Only polylines with `max |f| < 1` are reported, together with that
  maximum.

So the reported `m_upper` is the length of an explicitly exhibited path that has
passed a dense containment test; the residual error is that a 500-point sample
can miss a thin excursion above one, and the reported maxima are all within
`10^-5` of one, so this is a real caveat and the numbers are **not** certificates.
The direction of the discretisation error is: grid Dijkstra over-reports the true
geodesic, shortcutting removes most of that, and the result remains an upper
bound on `m(f)` only insofar as the containment test is sound.

Cross-check against the corpus bracket for the extremal family. At `n = 6`,
`r = 0.9999`, [TrueGeodesicLab.md](TrueGeodesicLab.md) gives the exact lower
bound `2(r - eps) = 1.4190` with `eps = (1 - r^n)^(1/n)`, and
[CrossingChordUpperBound.md](CrossingChordUpperBound.md) gives the exact upper
bound `2r - 2 eps tan(pi/4 - pi/(2n)) = 1.6644`. The lab returns `1.54269`,
inside the bracket. At `n = 7`, `r = 0.9999` the bracket is `[1.2914, 1.5546]`
and the lab returns `1.41496`, again inside; at `n = 8`, `r = 0.9999` the
bracket is `[1.1796, 1.4518]` and the lab returns `1.30425`. The same check
passes at `n = 3, 4, 5`.

## 1. The extremal landscape

Maximisation of `m_upper` over root configurations constrained to
`max_k |a_k| <= 0.9999`, seeded from the regular `n`-gon at four radii, from
angular and radial perturbations of it, from uniform random configurations, and
from the hardest configurations of section 2, followed by a local search.

| n | `sup m_upper` | `2 R*` | ratio | maximiser | `Var` | `mu` | `D` |
|---|---|---|---|---|---|---|---|
| 3 | 1.94323 | 2.00076 | 0.97125 | regular triangle, `r = 0.9999`, angular deviation `8.3e-4` | 0.99980 | 0.99968 | 0.99940 |
| 4 | 1.81836 | 1.99980 | 0.90927 | regular square, `r = 0.9999`, angular deviation `0` | 0.99980 | 0.99960 | 0.99880 |
| 5 | 1.67816 | 1.99980 | 0.83916 | regular pentagon, `r = 0.9999`, angular deviation `0` | 0.99980 | 0.99950 | 0.99800 |
| 6 | 1.54269 | 1.99980 | 0.77142 | regular hexagon, `r = 0.9999`, angular deviation `7e-16` | 0.99980 | 0.99940 | 0.99700 |
| 7 | 1.41496 | 1.99980 | 0.70755 | regular heptagon, `r = 0.9999`, angular deviation `4e-16` | 0.99980 | 0.99930 | 0.99581 |
| 8 | 1.30425 | 1.99980 | 0.65219 | regular octagon, `r = 0.9999`, angular deviation `4e-16` | 0.99980 | 0.99920 | 0.99442 |

`R*` is the radius of the minimum enclosing circle of the root set, and the ratio
is `m_upper / (2 R*)`.

Two things are worth stating precisely.

* **The maximiser is the regular `n`-gon at the largest permitted radius, at
  every degree tested.** The searches start from three different families,
  including uniform random configurations that reach `m_upper` values as low as
  `0.14`, and every one of them ends on the `n`-gon at the radius cap. The
  angular gaps at the returned maximiser are equal to `2 pi/n` to machine
  precision at `n = 4` through `n = 8`.
* **The table is a snapshot at a pinned radius, not a supremum.** The radius
  ladder on the exact family `z^n - r^n` is

  | n | `r = 0.9` | `0.99` | `0.999` | `0.9999` |
  |---|---|---|---|---|
  | 3 | 1.55885 | 1.75622 | 1.87925 | 1.94020 |
  | 4 | 1.27279 | 1.49348 | 1.68990 | 1.82229 |
  | 5 | 1.05801 | 1.28143 | 1.50835 | 1.68038 |
  | 6 | 0.90000 | 1.10494 | 1.34774 | 1.54626 |
  | 7 | 0.78099 | 0.96582 | 1.20866 | 1.41892 |
  | 8 | 0.68883 | — | 1.09394 | 1.30912 |

  and the corpus already proves that this tends to `2 r -> 2` at every degree
  (negative result 37; the exact bracket cited above). So the supremum of `m(f)`
  is `2` in every degree, approached along `r -> 1`, and the degree dependence in
  the table is entirely the `eps = (1 - r^n)^(1/n)` term at a fixed radius, not a
  degree-dependent ceiling. **No configuration in any search reached `m_upper`
  above `2`**, which is the falsification content of this section.

  The missing `n = 8`, `r = 0.99` entry is a method limitation, not a datum: on
  the `N = 201` grid the Dijkstra path for that configuration did not survive the
  containment verification, so no verified upper bound is reported there.

## 2. The chordless region

`J(a) = min over root pairs of max_{[a_i,a_j]} |f|`, so `J > 1` says no straight
root chord lies in `{|f| < 1}`. Direct adversarial maximisation of `J` over
`max_k |a_k| <= 1 - 10^-6`:

| n | `sup J` found | `D` | `mu` | `Var` | least pair distance |
|---|---|---|---|---|---|
| 3 | > 1 (common) | 0.79017 | 0.88891 | 0.92450 | 1.66534 |
| 4 | 1.03032 | 0.94809 | 0.89543 | 0.99607 | 1.25208 |
| 5 | > 1 (common) | 0.66905 | 0.83943 | 0.98040 | 0.93842 |
| 6 | 1.03613 | 0.92599 | 0.84553 | 0.99921 | 0.83892 |
| 7 | > 1 | 0.84071 | 0.87338 | 0.99357 | 0.75577 |

The chordless region is nonempty at every degree tested, **including even
degrees**. An earlier near-Fekete-seeded census in this lab found none at
`n = 4, 6, 8`; that was a basin artefact, and only the direct maximisation of `J`
enters the region. This is the recurring lesson of negative result 28 and it is
recorded here as a correction to this lab's own first pass, not as a property of
the problem.

Statistics of the chordless region as located:

* `max_k |a_k| > 0.987` in every instance found, and `> 0.9999` in most.
* `Var > 0.92` in every instance found. The measured variance floor is
  `0.9244988` at `n = 3` — exactly `(8/9)^(2/3)`, the closed form of Lemma 6 in
  [CentroidVarianceChordChart.md](CentroidVarianceChordChart.md), reproduced to
  seven digits by the search — `0.9793279` at `n = 5`, and `0.9867569` at
  `n = 7`. The proved chart threshold `(n-1)/(2n-1)` is `0.4`, `0.4444` and
  `0.4615` there, so the chart gives away roughly half the variance range that
  the geometry actually allows.
* `D` between `0.67` and `0.95`. This is far above generic (a random degree-6
  configuration has `D` near `6e-6`) and far below the hub-obstruction witnesses
  of [HardRegimeIsNearFekete.md](HardRegimeIsNearFekete.md), which sit at
  `D > 0.99994`. The chord obstruction and the hub obstruction are therefore at
  different distances from the Fekete maximiser, and one should not be described
  by the other's shell.

## 3. The composed cover was never defeated

Census objective: maximise `mu` subject to (i) no contained straight root chord
and (ii) no hub `h` in `{0, centroid} union {critical points}` carrying two
contained straight spokes. Seventy restarts of five hundred local steps per
degree, from both near-Fekete and uniform seeds.

| n | configurations found meeting (i) and (ii) |
|---|---|
| 3 | 0 |
| 4 | 0 |
| 5 | 0 |
| 6 | 0 |
| 7 | 0 |
| 8 | 0 |

Zero at every degree tested. Combined with section 2, which shows condition (i)
alone is easy to satisfy, the measurement says the canonical hub set repairs
every chordless configuration this lab could construct. That is a statement about
this search, not a theorem, and the corpus already contains exact witnesses where
individual members of that hub set fail: negative result 27's near-Fekete quintic
kills every critical hub and is rescued by the origin, while the exact MEC
falsifier of `AdaptiveMecDichotomyLab.md` kills chord-plus-origin and is rescued
by a critical hub. The census is consistent with both: it is the *union* that was
never defeated.

## What to take from this

* The straight-chord mechanism is much stronger than the corpus's single
  `n = 3` counterexample suggests. It covers every uniformly random configuration
  sampled at degrees 3 to 8, and its failure region is a thin shell at
  `max_k |a_k|` within `10^-2` of one.
* Inside that shell the failure is not confined to odd degree and is not
  asymptotically near-Fekete.
* The variance chart of
  [CentroidVarianceChordChart.md](CentroidVarianceChordChart.md) is provably
  correct but numerically conservative: the honest gap in its own coordinate is
  `Var in [(n-1)/(2n-1), V_n)` with `V_3 = (8/9)^(2/3)` exactly and
  `V_5 = 0.97933`, `V_7 = 0.98676` measured.
* The smallest concrete open sub-statement this lab isolates is section 3 turned
  into a claim: *every squarefree monic `f` with roots in the open unit disc has
  either a contained straight root chord, or a hub in `{0, centroid} union
  {critical points}` with two contained straight spokes.* It is not proved here,
  it is not implied by anything in the corpus, and the corpus contains exact
  witnesses killing each disjunct separately but none killing the disjunction.

## Replay

The lab scripts are session scratch and are not part of the corpus. The exact
statements they surround are replayed by

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_centroid_variance_chord_chart.py
```

which carries the Lemma 6 cubic-chord polynomial, the even-degree diameter chord,
the Corollary 3 sharp configuration, and the section 4 refutation of that note.
