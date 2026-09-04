# Reciprocal sweeping: a useful neighbor and a hard boundary

## Source and scope

Venkata Siddharth Pendyala, *Shortest paths in polynomial lemniscate
sublevel sets and a problem of Erdős*, arXiv:2606.19178v1 (17 June 2026),
studies a different Erdős problem.  For a monic degree-`n` polynomial with
zeros in the closed unit disk, it asks for the worst shortest path from zero
to the unit circle inside

```text
{|z|<=1, |f(z)|<=1}.
```

The paper proves upper bound `pi*n` and a lower bound of order
`sqrt(log n)`.  It neither states nor proves Erdős #1041, whose endpoints must
be two polynomial zeros and whose target constant is two.  The downloaded
primary PDF, abstract, and extracted locators were checked on 2026-08-27; this
note records only the parts that bear directly on the live #1041 mechanisms.

Primary source: <https://arxiv.org/abs/2606.19178>.

## Downloaded-source boundary

The primary PDF used for this note is arXiv:2606.19178v1, *Shortest paths in
polynomial lemniscate sublevel sets and a problem of Erdős*, by Venkata
Siddharth Pendyala, dated 17 June 2026. It was downloaded from
<https://arxiv.org/pdf/2606.19178v1>; the arXiv API record is
<https://export.arxiv.org/api/query?id_list=2606.19178>. The downloaded
34-page PDF had SHA-256
`d7902a8bc37d2aad6dea52dffbbbaaf7ff23954ece5a0c4cbab108f58df4e6df`.

The abstract (printed p. 1, extracted PDF lines 12--32) and Theorem 1.2
(printed pp. 3--4, extracted lines 97--113) support the stated bounds
`c sqrt(log n) <= S(n) <= pi n` and the qualitative unboundedness claim. The
introduction distinguishes this marked-point-to-boundary problem from the
Erdős--Herzog--Piranian root-to-root problem (printed pp. 2--3, extracted lines
51--78); it also identifies the alternating-maze lower-bound mechanism and
reciprocal-sweeping upper-bound mechanism (extracted lines 79--96). The upper
bound's exact source machinery is Section 9: the reflected-factor identity and
containment are printed pp. 27--28 (extracted lines 1462--1492), the Crofton
estimate is Lemma 9.1 on printed p. 28 (lines 1517--1546), and the nodal exit
argument culminates in Proposition 9.7 on printed pp. 30--31 (lines
1631--1705).

The source therefore supports the neighboring marked-point result and the
linear reciprocal-sweep bound only. It does not state Erdős #1041, a
root-to-root path, a degree-free bound, or any transfer of the alternating
maze to the first-merge problem. The reciprocal-sweep skeleton and the three
transfer questions below are this repository's source-assimilation and
boundary analysis; no theorem is imported into Lean here.

## The reciprocal sweep

For

```text
f(z) = product_j (z-a_j),   |a_j|<=1,
```

put

```text
g(z) = product_j (1-conj(a_j) z).
```

The factor identity

```text
|1-conj(a)z|^2 - |z-a|^2
  = (1-|z|^2)(1-|a|^2)
```

gives `|f(z)|<=|g(z)|` in the closed unit disk.  Since `g` has no zero in the
open disk and `g(0)=1`, `u=log|g|` is harmonic there and its zero-level
component through zero reaches the unit circle.  The real algebraic curve

```text
|g(x+iy)|^2-1=0
```

has degree at most `2n`.  A line meets it at most `2n` times, so Crofton gives
total length at most `2*pi*n`; two edge-disjoint exits from the origin nodal
component give one exit of length at most `pi*n`.  Along that exit
`|f|<=|g|=1` (strictly inside the disk when every root is interior).

This is a valid positive skeleton in this repository's #1041 assimilation. It
is not yet a root-to-root path: the distinguished point is zero, the nodal skeleton
need not contain any root, and the Crofton budget is linear in the degree.
Any #1041 use must add a root-attachment or root-averaging theorem that reduces
that linear budget to a single pair below two.

## Why arbitrary-lobe length is not available

The lower-bound half of the same paper constructs alternating circular mazes
and realizes their forbidden arcs by monic polynomials whose zeros lie on the
unit circle.  Every path from zero to the boundary inside the resulting
sublevel set has length at least `c*sqrt(log n)`.

This does not falsify the first-merge Newton conjecture: it does not identify
the minimum critical pair and it does not lower-bound any root-to-root path.
It does rule out a tempting analytic shortcut.  Neither root confinement nor
polynomial lemniscate structure gives a degree-free intrinsic-length bound for
an arbitrary marked-point-to-boundary route.  In particular, the remaining
first-merge proof must use the critical ordering, two-root endpoint structure,
or an averaging charge across the degree; general univalent-domain geometry
is insufficient.

## Live transfer questions

1. Can reciprocal sweeping be centered or normalized at a root while retaining
   a degree-free length charge?
2. Can the `2*pi*n` nodal length be charged to `n` root attachments so that one
   pair costs at most two, rather than `pi`?
3. Does the alternating-maze quantization make the stronger first-merge bound
   `L_1+L_2<=2|f(c)|^(1/n)` fail at high degree?

The existence precondition in question 1 is now settled: a root-centred sweep
is available by the ordinary resultant identity in
[RootCentredReciprocalSweep.md](RootCentredReciprocalSweep.md), with its
28,000-configuration replay recorded there. What remains open is the
degree-free length charge, not the existence of a root at which to centre.

The third question has a dedicated numerical falsifier in
`scripts/search_counterexample.py`.  A subthreshold run is not evidence that
the maze cannot be transferred.

## Claim ceiling

This is a source-assimilation and mechanism-boundary note.  It imports no
theorem into Lean, proves no new path bound, and does not change the open status
of Erdős #1041.
