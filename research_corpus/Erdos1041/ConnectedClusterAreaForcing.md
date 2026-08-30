# Fixed-level area forcing for connected lemniscate clusters

## Status

This note proves a global pigeonhole theorem that composes the connected-cluster
Bergman certificates across **all** multi-root components of one regular
lemniscate level.  It handles arbitrary simultaneous ties and requires no
choice of a marked critical hub.  It does not prove that its scalar forcing
condition always holds, and it does not prove unrestricted Erdős #1041.

The companion computation decisively falsifies the universal version of the
scalar condition in the near-regular-polygon shell.  That failure does not
refute the sharper component certificate, because actual component areas can
be much smaller than the global area budget.

## The theorem

Let `0<t<1` be a regular value of a monic degree-`n` polynomial.  List the
components `C_i` of `K_t={|f|<t}` that contain at least two distinct root
locations.  Write

```
k_i     = number of roots in C_i, with multiplicity,
q_i     = max_{c in C_i, f'(c)=0} |f(c)|/t,
alpha_i = Area(C_i)/(pi t^(2/n)),
L_i     = log((1+q_i^(2/k_i))/(1-q_i^(2/k_i))).
```

The connected-cluster Bergman theorem gives a curve in `C_i` with

```
length_i^2 <= 2 t^(2/n) alpha_i L_i.                 (1)
```

The components are disjoint, and Pólya's area-capacity inequality gives

```
sum_i alpha_i <= Area(K_t)/(pi t^(2/n)) <= 1.        (2)
```

Therefore

```
sum_i 2/L_i >= 1                                     (AF)
```

forces `alpha_i L_i<=2` for at least one component.  Otherwise every
`alpha_i>2/L_i`, whose sum contradicts (2).  Equation (1) then supplies two
roots joined inside `K_t` by a curve of length at most `2 t^(1/n)<2`.
The finite pigeonhole implication itself does not need `alpha_i>=0`; geometric
nonnegativity is available but logically redundant once (2) is known.

The finite-sum implication and its exact composition with
`ConnectedClusterBergman.length_le_two_of_cluster_certificate` are checked in
`ConnectedClusterAreaForcing.lean`.

## Merge-tree form

For simple, distinct critical levels, a component born at merge level `beta`
and observed at level `t` has `q=beta/t`.  Between consecutive merge levels,
the left side of (AF) is an explicit increasing scalar function.  Its maximum
up to level one is therefore attained immediately below a merge or at level
one.  A union-find pass over the descending-branch merge tree evaluates every
candidate without estimating a component area or capacity.

The deterministic probe reports area-forcing maxima above one on three bulk
configurations:

```
degree 4: 2.2625...
degree 6: 3.0390...
degree 8: 1.2920...
```

Thus the theorem genuinely converts merge data into a short-path certificate
on those rows.

## Exact failure boundary of this mechanism

The same scalar condition is not universal.  For radius `0.999` angular
perturbations of regular polygons at perturbation scale `10^-3`, deterministic
rows at degrees `4,6,8,10` have maximal (AF) scores approximately

```
0.3049, 0.2739, 0.3046, 0.6395.
```

All are below one.  The branch continuations return complete `n-1` edge trees
and satisfy the recorded endpoint and level residual gates.  These are
numerical falsifiers of universal **area-sum forcing**, not counterexamples to
the connected-cluster theorem, CDF, or Erdős #1041.

The structural lesson is sharp.  Merge order and critical-value ratios alone
do not force CDF near equality; one must spend either the actual component area
defects, the exact Green/capacity defects, or a separate near-Fekete path
mechanism.  Repeating a purely scalar merge-level argument cannot close that
shell.

## Replay

```sh
python3 research_corpus/Erdos1041/scripts/check_erdos1041_connected_cluster_area_forcing.py --json
```
