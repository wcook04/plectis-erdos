# Every low tied Newton face merges two negative ends by level zero

## Status

This is an all-degree analytic theorem for the homogeneous low-mode models
left open by `NearFeketeUniqueNewtonFaceClosure.md`.  It proves the missing
**topological** connector: every model has a component of `{Re Q<=0}` carrying
at least two of its asymptotic root-direction ends.  It does not yet prove that
the connecting curve has the strict renormalized metric saving required by
Erdős #1041.

The load-bearing finite trace algebra and the selection of a nonpositive real
critical value are Lean checked in `TiedNewtonFaceCriticalTrace.lean`.

## 1. The critical-value trace

Let

```text
Q(z) = sum_(m in M) A_m z^m - z^n,
1 <= m < n/2 for every m in M,
```

with arbitrary complex coefficients, not all zero.  List the `n-1` critical
points `c_1,...,c_(n-1)` with multiplicity.  Then

```text
                     sum_i Q(c_i) = 0.                    (1)
```

This is forced by the missing upper half of the coefficient vector.
Put `N=n-1` and `M_0=max M`.  The monic derivative is

```text
Q'(z)/(-n) = z^N + sum_(m in M) (-m A_m/n) z^(m-1).       (2)
```

All its coefficients in degrees `M_0,...,N-1` vanish.  If
`S_k=sum_i c_i^k`, Newton's identity gives

```text
S_k + a_(N-1)S_(k-1) + ... + a_(N-k+1)S_1 + k a_(N-k)=0.
```

For `1<=k<=M_0`, every coefficient on the right is in that zero block:

```text
N-k >= n-1-M_0 >= M_0,
```

where the last inequality is exactly `2M_0<=n-1`.  Hence

```text
S_m=0 for every active m.                                (3)
```

At a critical point, the derivative equation says

```text
n c^n = sum_m m A_m c^m,
```

so

```text
Q(c) = sum_m (1-m/n) A_m c^m.                            (4)
```

Summing (4) and using (3) proves (1).  Therefore at least one critical
point satisfies

```text
                         Re Q(c) <= 0.                    (5)
```

The conclusion includes equality and multiple critical points; no genericity
assumption is needed.

## 2. From the trace to a genuine merge

Write `H=Re Q` and take a critical point `c` supplied by (5), with
`h=H(c)<=0`.  If `c` has multiplicity `r` as a zero of `Q'`, the local harmonic
normal form has `r+1` negative sectors of `{H<h}` meeting at `c`.

Every component of `{H<h}` is unbounded.  Otherwise, on a bounded component
the harmonic function `H-h` would vanish on the boundary and be strictly
negative inside, contradicting uniqueness for the Dirichlet problem.  Outside
a sufficiently large disk, `{H<h}` has exactly the `n` disjoint negative
sectors of `-Re(z^n)`.

Now follow the local negative sectors at `c` outward.  If two already lie in
one open component, that component has two different ends.  Otherwise their
distinct component closures meet at `c`, so `{H<=h}` joins their distinct
ends.  In either case, because `h<=0`, two asymptotic root-direction ends are
joined inside

```text
                            {Re Q <= 0}.                   (6)
```

Thus the all-degree tied-face obstruction is no longer topological.  A safe
curve always exists.

## 3. What remains is a scattering-length inequality

Let the two connected ends be cut at large scaled radius `R`, and let `L(R)`
be the shortest length inside `{H<=0}` joining their cut points (allowing the
natural asymptotic arms).  Finite transfer to the near-Fekete polynomial needs

```text
                         L(R) < 2R                        (7)
```

for some finite `R`.  The trace theorem proves connectivity but not (7): an
arbitrary compact core can in principle add a positive renormalized length.
Calling (6) a proof of Erdős #1041 would therefore be wrong.

There is nevertheless a sharper candidate than the previous free-connector
search.  A deterministic bounded probe selects a critical point with
`Re Q(c)<=0`, two straight arms from `c` to root-direction rays, and the two
outward ray tails, while charging the exact defect

```text
|R omega^j-c| + |R omega^k-c| - 2R.
```

For seed `20260825`, 16 models in each degree `5,...,9` gave zero sampled
failures.  The worst best sampled scores were respectively

```text
-0.01533, -0.13027, -0.02035, -0.04168, -0.06641.
```

This is evidence only: sampled segment maxima do not certify containment, and
the unrestricted critical-spoke mechanism is known to fail elsewhere in the
corpus.  Its value is that the trace has supplied a mathematically forced hub
selector specific to the sparse face, rather than another unconstrained
connector atlas.

## 4. Consequence for the near-Fekete programme

The local programme now has a clean division:

1. unique outer faces close by the existing integer-gap spoke theorem;
2. every tied low face has a two-ended safe component by the trace theorem;
3. the only model-level residual is the strict scattering-length inequality
   (7), or an exact counterexample to it;
4. if (7) holds throughout the compact normalized face space, the existing
   positive Newton-weight gaps transfer it to analytic arcs, and semialgebraic
   curve selection promotes the arc theorem to a neighbourhood.

This replaces “construct a connector somehow” by one precise metric question
on a canonically selected negative critical merge.

## Replay

```sh
python3 research_corpus/Erdos1041/scripts/check_erdos1041_tied_newton_face_critical_trace.py --json
python3 research_corpus/Erdos1041/scripts/check_erdos1041_tied_newton_face_critical_trace.py --metric-probe --json
```
