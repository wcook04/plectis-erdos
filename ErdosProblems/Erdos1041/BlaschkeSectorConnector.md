# Blaschke-sector connector (ordinary r6 companion)

Ordinary note, 2026-09-07, Type B r6 return. Type A applied the twelve
hash-guarded short-note edits that display the already registered scaling
corollary. The uniform quadratic-sector connector, the degree-24 length
bound, and the two-sided cusp law remain ordinary advisory proofs: they
are not inserted into the live short note, novelty is not established,
and they are not Lean-checked. The Lean file is an uncompiled scalar
interface. Erdős #1041 remains open.

Replay (this wave):

```sh
./repo-python Erdos1041/scripts/check_r6_constants.py
./repo-python Erdos1041/scripts/check_symbolic_identities.py
./repo-python Erdos1041/scripts/check_erdos1041_angular_budget_closure.py --quick
```

Complete ordinary proofs live in
[BlaschkeSectorConnector_r6_source.tex](BlaschkeSectorConnector_r6_source.tex).
Packet README: [r6_README.md](r6_README.md).
Lean (UNCOMPILED): [BlaschkeSectorConnector.lean](BlaschkeSectorConnector.lean).
Long-record lag destinations (not a frozen-R edit):
[r6_long_record_lag.md](r6_long_record_lag.md),
[r6_long_record_transfers.md](r6_long_record_transfers.md),
[r6_lag_companion.md](r6_lag_companion.md).

## Registered scaling (displayed in the live note)

Already Corollary B'' of [AngularBudgetLowCriticalClosure.md](AngularBudgetLowCriticalClosure.md):
every squarefree monic polynomial has a connection of length less than
`2((25/13) μ)^{1/n}` in the open level `(25/13) μ`. In every degree the
length can be chosen less than `(5/2) μ^{1/n}` (use `(25/13)^{1/3} < 5/4`
for `n ≥ 3`, and the exact root segment of length `2√μ` in degree two).
This is a consequence of the live 13/25 theorem, not a new theorem of
this review. The 71/10 argument is retained as an independent area
construction, not described as numerically strongest.

## Advisory ordinary theorems (not flagship)

The source report proposes, with complete ordinary proofs not independently
reviewed here:

1. **Uniform quadratic-sector connector.** For every `N ≥ 3` and
   `0 < b ≤ 1/(10N)`,
   `F_{N,b}(z) = [z(z+b)]^N - (1+bz)^N` has an explicit three-piece
   connection of length at most `2 - (689/1050) t < 2` at level
   `exp(-λ t/25) < 1`, where `λ = Nb` and `t = (2λ/5)^{1/(2N-1)}`.
   This removes the unspecified starting degree of the r5 asymptotic
   connector, in the stated parameter range. Not Lean-checked.

2. **Degree-24 length below one half.** The existing r5 high-critical
   certificate (`N=12`, `b=1/120`, `r=999999999/10^9`) already has
   `μ > 11/12` and fails every displayed radius-`4/3` centre test.
   Combining it with the sector path gives length
   `< 58672129/117936000 < 1/2` at level `≤ 3750/3763 < 1`.
   This is an easy metric example outside those scalar regimes, not a
   parent counterexample.

3. **Two-sided fixed-degree cusp.** Retaining the perturbation's zero at
   the origin gives barriers at radius `δ^{1/(n-1)}`. Together with the
   connector, `2 - Λ(F_{N,b}) ≍ δ_b^{1/(n-1)}` in every fixed even
   degree `n ≥ 6`. This excludes a local Hölder estimate with exponent
   greater than `1/(n-1)` at `z^n-1` on the full closed-root-disc class.
   It does not establish a Hölder upper modulus for arbitrary
   perturbations, or a leading cusp constant.

## Lean boundary

[BlaschkeSectorConnector.lean](BlaschkeSectorConnector.lean) states
norm-defect, disc-retention, pullbacks, amplitude, scalar length
consolidation, reverse-triangle barrier, exact degree-24 comparisons,
and `(25/13) < (5/4)^3`. It does not formalise holomorphic square-root
choice, path integration, sector topology, root continuity, or `Λ`.
Parent serial fan-in owns compilation. No Comparator run this wave.

## Lead judgement

Title and Theorem 1 (all-degree monic trinomials) stay. The live centre
has not moved: the new connector and cusp are ordinary family theorems,
not a complete all-degree parent-length family. Keep `71/10`, `13/25`,
and disk-family `S=4/3`. The geometric remaining question is still
`Λ(f) ≤ 2`.
