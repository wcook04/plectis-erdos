# Erdős 257 selected-ancestry tail-survival audit

## Claim boundary

Erdős problem 257 remains open.  This audit does not prove that `1/2` is a
Mersenne achievement value.  It corrects the selected-ancestry proof target:
the previously isolated inequality `B_N > 0` is sufficient, but it is not
necessary.

The proof-bearing source is
`ErdosProblems/Erdos257/SelectedAncestryTailSurvival.lean`.

## 1. The exact weaker budget

Write

\[
  B_N=2^{-N}-r_N,
  \qquad
  E_N=\operatorname{mersenneTail}(N)-2^{-N},
\]

where `r_N` is the pinned greedy remainder for `1/2`.  Define the complement
budget

\[
  C_N=B_N+E_N.
\]

Then exactly

\[
  \boxed{C_N=\operatorname{mersenneTail}(N)-r_N.}
\]

The distinction is important.  `B_N>0` asks for the stronger dyadic ceiling
`r_N<2^{-N}`.  Exact achievement-set survival asks only

\[
  r_N\leq\operatorname{mersenneTail}(N),
\]

or equivalently

\[
  B_N\geq-E_N.
\]

Every complete Mersenne tail is irrational, while `B_N` and `2^{-N}` are
rational.  Equality cannot occur.  Hence the exact condition is the strict
but weaker inequality

\[
  \boxed{B_N>-E_N.}
\]

## 2. All-scale deterministic law

The complement budget has a particularly simple orbit law:

\[
 C_{N+1}=
 \begin{cases}
 C_N,&\text{if rank }N+1\text{ is taken},\\
 C_N-w_{N+1},&\text{if rank }N+1\text{ is skipped}.
 \end{cases}
\]

Thus takes preserve the remaining complement mass and skips spend exactly
one Mersenne coin.  Fatality is not a failure to maintain the sharper dyadic
phase.  It is the first skip that overspends this complement account.

The new Lean source packages the exact endpoint as
`HalfSelectedAncestryTailSurvival` and states the equivalence

\[
  \frac12\in\mathcal A
  \quad\Longleftrightarrow\quad
  \forall N,\ C_N>0
  \quad\Longleftrightarrow\quad
  \forall N,\ B_N>-E_N.
\]

Its focused build passed all `3020` jobs.  The printed axiom audit contains
only the project's standard `propext`, `Classical.choice`, and `Quot.sound`.

## 3. Relation to the full-shell producer

The source-current first-window bridge remains correct, but its producer is
strictly stronger:

\[
  \operatorname{frozenMargin}(N-1,N)\geq0
  \Longrightarrow B_N\geq0
  \Longrightarrow B_N>-E_N.
\]

Consequently a proof of `HalfGreedySkippedFullShellNonnegative` still solves
the half case, but it is no longer the weakest selected-ancestry target.
Arguments may allow recoverable negative `B_N`; they only have to exclude a
negative crossing whose magnitude reaches the entire future correction tail.

## 4. Computation boundary

The existing exact replay through rank `100000` found `B_N>0` everywhere, so
it also verifies `C_N>0` on that bounded range.  That run does not distinguish
the weaker theorem from the stronger ceiling conjecture.  Extending the same
horizon without a proposed first-fatal-borrow lemma therefore has negligible
information value.

The next useful computation must discriminate an analytic decomposition of a
putative overspending skip—for example by retaining the last selected
denominator ancestry responsible for the pre-skip value of `C_N`.  Scalar
interval, parity, and reduced-denominator data have already been shown
compatible with the fatal sliver.

## 5. Surviving obligation

The exact selected-ancestry obligation is now:

> Prove that no actual greedy skip spends more than the current complement
> budget, equivalently `B_N > -mersenneCorrectionTail N` at every depth.

This is the original null-fibre arithmetic boundary in its weakest budget
coordinate.  It remains unproved.

## 6. Fatal-borrow transfer to the quotient packet

The proof-bearing module
`ErdosProblems/Erdos257/FatalBorrowMidpointTransfer.lean` now removes the
coordinate gap between this weakest budget boundary and the existing seam
machinery.

Suppose rank `d` is genuinely skipped and the complement budget at depth
`d` is nonpositive.  Irrationality of the complete Mersenne tail makes the
budget inequality strict.  The exact frozen-margin identity then gives

\[
  \operatorname{margin}(d-1,d)
   = 2^{2d}B_d-\Phi_{A_{d-1}}(2d)<0.
\]

Lean now proves the converse first-shell accounting law: every negative
full-shell margin determines a natural number `R` with

\[
 Q_{A_{d-1}\cup\{d\}}(2d)+R=2^{2d-1}.
\]

Thus a fatal borrow forces an exact target-zero midpoint quotient row.  The
actual skip also forces the inserted prefix strictly above `1/2`, so the
separate analytic crossing premise in the older second-shell theorem is
automatic.  The resulting failure packet is the exact dichotomy

1. `R = 0`, an exact zero-residual midpoint row; or
2. `R >= 1`, with exact seam-word alignment, seam remainder `R+1`, and for
   every admissible logarithmic lookahead `L`,

   \[
     (R-1)2^L <
       \operatorname{finiteCoeffWindowNumerator}
         (A_{d-1}\cup\{d\},2d,L).
   \]

The focused build passed all `3048` jobs, and the new axiom audit contains
only `propext`, `Classical.choice`, and `Quot.sound`.

This does not yet exclude a fatal borrow.  It does, however, eliminate the
large reduced denominator from the remaining failure analysis altogether.
The zero-residual branch is narrowed further in Section 7 below; the
positive-residual branch still requires a contradiction to its second-shell
incidence certificate.  This agrees with the cyclotomic denominator audit:
cancellation does not make the remainder coordinate small enough for a
separation proof, so the live route must stay in quotient and defect
variables.

### Zero-residual fixed-anchor falsifier

The first attempted exclusion of the `R = 0` branch is false for a structural
reason.  From a zero residual one gets full-shell margin `-1`.  It is tempting
to combine fatality with the permanently selected anchors
`{2,3,6,7,14,...}` and prove

\[
  2^{2d}\operatorname{mersenneCorrectionTail}(d)
   +\Phi_{\text{anchors}}(2d)\ge1.
\]

Exact residue evaluation falsifies this already for
`{2,3,6,7,14}`: on common-multiple phases the expression approaches `3/4`.
Adding any fixed finite anchor set cannot repair the mechanism.  Simultaneous
residue-zero phases reduce the anchor contribution to its Mersenne subseries
value, at most `1/2`, while the scaled correction tail approaches `1/3`.
Therefore the zero-residual row must be attacked through moving selected
ancestry or seam dynamics, not a uniform floor from finitely many early
digits.

## 7. Zero residual is exactly a surviving cofinite carry cell

The proof-bearing module
`ErdosProblems/Erdos257/FatalBorrowCofiniteCarryTransfer.lean` now connects
the midpoint residual to the mature cofinite carry machinery.  Complete the
actual lower word below `d` by the full open tail `(d,\infty)`.  Lean proves
the exact identity

\[
 e_{2d+1}=4R+3-P_d,
\]

where `P_d` is the paired boundary pulse of the forced seam-greedy word.
This is the quotient-to-defect coordinate change selected by the denominator
no-go: it uses the exact support swap rather than a separation estimate on
the rational remainder.

For `R=0`, the seam remainder is exactly one and

\[
 e_{2d+1}=3-P_d.
\]

At a mature fatal row (`d\ge13`), the cofinite completion lies strictly below
`1/2`.  The centred carry is therefore nonnegative, while the existing
cofinite endpoint theorem says it cannot be zero.  The permanently selected
rank `2` supplies at least one pulse unit.  Consequently Lean proves

\[
 \boxed{P_d\in\{1,2\}}.
\]

Equivalently, a fatal zero-residual midpoint row has producer carry exactly
`-1` or `-2`.  It cannot occupy cell `-3`, and it is not a fourth exceptional
mechanism.  The remaining zero-row work is now the existing arithmetic of
the two surviving cells under the additional unit seam-remainder constraint.

The focused build and final serialized authority check pass.  The three new
declarations are:

- `midpointRow_lazyCenteredCarry_eq_four_mul_residual_add_three_sub_pulse`;
- `midpointZeroRow_lazyCenteredCarry_eq_three_sub_pulse`;
- `nonpositiveComplementBudget_midpointZero_forces_pulse_one_or_two`.

Their printed axiom audits contain only `propext`, `Classical.choice`, and
`Quot.sound`.

## 8. Fatal rows collapse to the existing middle row-escape producer

The proof-bearing modules
`ErdosProblems/Erdos257/FatalBorrowPositiveResidualPacket.lean` and
`ErdosProblems/Erdos257/FatalBorrowMiddleScaleContradiction.lean` now remove
the former two-branch endpoint split.

For every mature fatal borrow, the midpoint residual satisfies

\[
 R<2\sqrt{2d}+3,
 \qquad
 \operatorname{seamRemainder}(d)=R+1<d.
\]

The second inequality makes row `d` an upper-or-middle reset.  It cannot be
upper: the adjacent-cut carry theorem gives
`2^d < seamIntegerGreedyRemainder d`, contradicting the row-small bound.
Thus a fatal row is necessarily a middle reset.

At this point the weakest existing producer interface is already enough:

```text
SeamMiddleProducerRowEscape
```

It says that every mature middle-producer remainder is at least its row.
The new checked theorem
`nonpositiveComplementBudget_false_of_middleProducerRowEscape` consumes it
directly, contradicting `seamRemainder(d) < d`.  Independently, the older
`half_mem_mersenneAchievementSet_of_middleProducerRowEscape` theorem already
proves the global endpoint

```text
SeamMiddleProducerRowEscape
  -> (1 / 2 : ℝ) ∈ mersenneAchievementSet.
```

The stronger named middle-reset scale producer also gives a separate
fatal-row contradiction.  It forces

\[
 3\,2^{\lfloor(d+5)/2\rfloor}+2(d-2)\le 4(R+1).
\]

The square-root estimate is deliberately weakened to the linear envelope
`4(R+1) <= 16d+12`, while Lean proves

\[
 16d+12<3\,2^{\lfloor(d+5)/2\rfloor}
 \qquad(d\ge13).
\]

This is a contradiction.  Exact Lean evaluation proves positivity of the
complement budget below row thirteen, and a least-fatal-row argument proves
the stronger conditional endpoint

```text
SeamMiddleResetRemainderScaleProducer
  -> (1 / 2 : ℝ) ∈ mersenneAchievementSet.
```

The focused build and serialized authority check both pass; all printed
axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.

The selected-ancestry and critical-band lanes now also meet in a checked
contrapositive witness theorem.  The declarations

```text
nonpositiveComplementBudget_false_of_upperResetCriticalBandEscape
exists_upperResetCriticalDanger_of_nonpositiveComplementBudget
exists_upperResetCriticalDanger_before_of_nonpositiveComplementBudget
```

prove that a mature fatal borrow is incompatible with the all-depth critical
band producer and therefore emits some actual upper reset `s` whose nearest
critical index `j` satisfies

\[
  2^{s-j+1}<E_s+2(s+j).
\]

Criticality separately retains `E_s <= 2^(s-j+1)`, so this is exactly the
forbidden linear-width interval below the nearest dyadic boundary.  The
first-small-row proof has now been factored through the local theorem
`seamIntegerGreedyRemainder_ge_row_of_upperResetDyadicBandEscape_below`.
It consumes band certificates only at upper resets strictly below its target
row.  Consequently the stronger fatal-borrow theorem certifies `s < d`, not
merely a global obstruction.  The source-current last-ancestor theorem now
sharpens this further: it returns the final upper reset, the literal complete
right run of length `k`, and its row-small endpoint.

The new module `FatalCriticalDangerEndpointReduction.lean` pushes such a
danger through any actual upper/right run of length `k`.  If `j` is the
certified critical index, Lean proves the lossless dichotomy

\[
 k<j
 \quad\text{or}\quad
 R_{s+k+1}+C_k<4^k\,2(s+k),
\]

where `C_k` is the complete affine right-run pulse packet.  The first branch
is exactly an early termination before the critical scale; the second is a
linearly thin endpoint packet, with no discarded pulse or denominator error.
Equivalently, the endpoint lower envelope
`4^k * 2(s+k) <= R+C` forces `k<j`.  Therefore a fatal danger can be excluded
by two independent producer-side facts: the observed critical-index identity
`k=j`, and this endpoint lower envelope.  Neither fact is proved here; the
point is that the former diffuse forbidden interval now has only these two
explicit escape sockets.

For the actual last ancestor emitted by a fatal borrow, its danger already
uses the literal run length `k`.  The checked theorem
`exists_lastUpperAncestorThinPacket_of_nonpositiveComplementBudget` therefore
removes the dichotomy and returns both

\[
 R_{s+k+1}<s+k+1,
 \qquad
 R_{s+k+1}+C_k<4^k\,2(s+k).
\]

The live producer is now a single lower-envelope assertion for actual
last-ancestor packets.  Proving `4^k * 2(s+k) <= R+C` for those packets would
exclude every mature fatal borrow directly, without first proving the global
critical-index identity.

Lean now packages the exact all-depth version as
`SeamActualUpperRightPacketLinearEscape`.  It quantifies only over a literal
upper reset and a literal finite right-run recurrence and asks

\[
 4^k\,2(d+k)\le R_{d+k+1}+C_k. \tag{AP}
\]

The checked chain

```text
SeamActualUpperRightPacketLinearEscape
  -> no row-small seam state from row 13 onward
  -> SeamMiddleProducerRowEscape
  -> 1/2 in the Mersenne achievement set
```

ends in
`half_mem_mersenneAchievementSet_of_actualUpperRightPacketLinearEscape`.
This is strictly leaner as a producer interface than
`SeamUpperResetDyadicBandEscape`: the latter asks every upper reset to avoid
every hypothetical dyadic index `j`, while `(AP)` asks only for the packet at
the run length the orbit actually realizes.  No claim of a proof of `(AP)` is
made; the reduction removes unused scales from the obligation.

The scale endpoint is strictly weaker than the older two-sided
reset-square-root fan-in, because it removes the upper-reset charge floor.
It is nevertheless stronger than the row-escape endpoint that was already
present in the corpus.  The live analytic residual is therefore
`SeamMiddleProducerRowEscape`: exclude every mature row-small middle reset.
Existing corpus evidence says not to attack this by raw remainder
denominators or size descent: right predecessors can create fresh small
landings.  The remaining leverage is the exact upper/right endpoint packet
and its previous-middle staircase/pulse-register coordinate.

The denominator-cancellation audit sharpens the coordinate choice further.
Lean now proves
`seamActualUpperRightPacketLinearEscape_iff_successorLinearEscape`: after
dividing the exact terminal packet identity by its base-four scale, every
right-run pulse cancels.  Thus `(AP)` is equivalent to the immediate-successor
inequality

\[
  2^{d+1}-2^{d-k+1}+2(d+k)\le R_{d+1},                 \tag{AS}
\]

for the literal realized right-run length `k`.  The new named producer is
`SeamActualUpperSuccessorLinearEscape`, and
`half_mem_mersenneAchievementSet_of_actualUpperSuccessorLinearEscape`
consumes it directly.  This is the clean quotient/defect coordinate demanded
by Proposition C: it contains neither a reduced rational denominator nor an
accumulated pulse estimate.  A continuation should prove `(AS)` from the
ordered upper-reset ancestry (or falsify a named strengthening of it), not
re-estimate the raw greedy remainder and not separately bound the pulses that
cancel in the exact identity.
