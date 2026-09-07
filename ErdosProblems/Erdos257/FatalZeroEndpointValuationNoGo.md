# Fatal-zero endpoint valuation no-go

## Exact witness

The deterministic seam word at row

\[
s=1422
\]

has all of the endpoint arithmetic forced by the surviving fatal-zero
branch:

\[
s\equiv0\pmod 3,
\qquad P_s=1.
\]

It is also the endpoint of a literal two-step right run immediately after an
upper reset.  The two realized pulse digits are

\[
p_{1420}=9,qquad p_{1421}=7.
\]

Consequently their affine base-four charges satisfy the complete nested
unit-state congruences for that run:

\[
 1+(p_{1421}+4)=12\equiv0\pmod4,
\]

and

\[
 1+4(p_{1420}+4)+(p_{1421}+4)
 =64\equiv0\pmod{16}.
\]

Nevertheless its seam remainder is not one.  In fact it has bit length
1420 and satisfies the still stronger collision

\[
E_{1422}\equiv1\pmod{256},
\qquad E_{1422}\not\equiv1\pmod{512}.
\]

The exact integer-greedy reconstruction and all assertions above replay in
`scripts/check_erdos257_fatal_zero_endpoint_valuation_nogo.py`.

## What this rules out

`HalfSeamUnitRemainderAncestry.lean` proves that a unit endpoint forces every
terminal suffix charge of a right run to be `-1` at its corresponding
base-four scale.  The row-1422 witness proves the converse is false even
after adjoining all of the currently forced scalar fatal-zero data:

- mature phase zero modulo three;
- endpoint pulse one;
- an actual upper/right ancestry block;
- every suffix congruence through the full realized block.

Therefore no proof may promote those terminal congruences, or a bounded
2-adic refinement of the endpoint remainder, into a unit-state
characterization.  A successful exclusion must retain a noncongruence
coordinate: the exact Archimedean cylinder equality, the moving support-card
inequality, the multiplicity-window size/sign, or the analytic fractional
mass/fatality input.

This is an exact finite counterexample to a proposed implication, not a
counterexample to Erdős #257 and not a proof that unit seam remainders
exist.  The row does not satisfy the fatal midpoint or nonpositive-complement
budget hypotheses.

## Verification boundary

Evidence class: bit-exact deterministic computation from the defining greedy
algorithm.  The checker uses no floating point and no cached fixture.  This
result is not Lean-checked.

```text
tao_pipeline_receipt:
  input_stage: generation
  output_stage: verification
  artifact: FatalZeroEndpointValuationNoGo.md + exact checker
  human_understanding_delta: terminal base-four ancestry congruences are necessary but not sufficient even on the fatal phase/pulse slice
  verification_state: exact Python integer replay; not Lean
  publication_or_review_state: internal research note; not independently reviewed
  canonicalization_state: one subordinate no-go in the fatal-zero family
  unresolved_downstream_bottleneck: exclude E_s=1 using an Archimedean or moving-support inequality
  next_stage_owner: Erdős 257 fatal-zero frontier
```
