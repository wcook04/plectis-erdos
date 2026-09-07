# Fatal borrow to cofinite carry

## Purpose

The fatal-borrow midpoint transfer leaves two cases: a zero midpoint
residual `R = 0`, or a positive residual carrying the second-shell incidence
certificate.  The zero case looked like a separate exceptional row.  It is
not.

For the actual prefix below a skipped rank `d`, complete that lower word by
the full open right tail `(d, ∞)`.  The exact support swap already proved in
`HalfCylinderFinalMiddleCellEscape.lean` adds three to the centred carry.
Combining it with the midpoint-row seam alignment gives

\[
 e_{2d+1}=4R+3-P_d,
\]

where `P_d` is the seam word's paired boundary pulse.  Thus

\[
 R=0 \quad\Longrightarrow\quad e_{2d+1}=3-P_d.
\]

This identifies the midpoint-zero branch with the same `-3,-2,-1`
producer-cell geometry already governing the final-middle obstruction.
There is no independent zero-row mechanism left to analyse.

## Proof-bearing declarations

`FatalBorrowCofiniteCarryTransfer.lean` contains:

- `midpointRow_lazyCenteredCarry_eq_four_mul_residual_add_three_sub_pulse`;
- `midpointZeroRow_lazyCenteredCarry_eq_three_sub_pulse`;
- `nonpositiveComplementBudget_midpointZero_forces_pulse_one_or_two`.

The proof uses exact actual/seam word alignment, the support identity for the
actual seam word, the producer-carry affine formula, and the cofinite
support-swap theorem.  It introduces no new analytic hypothesis.

## Consequence for the live frontier

The zero residual is equivalently `seamIntegerGreedyRemainder d = 1`.  At a
mature fatal row the new consumer goes further: strict sub-halfness of the
cofinite completion, carry nonnegativity, the no-zero endpoint theorem, and
the forced rank `2` imply

\[
 P_d\in\{1,2\}.
\]

Hence its producer carry is exactly `-1` or `-2`.  The most discriminating
next questions are now:

1. can seam remainder `1` be excluded at every mature rank; or
2. can the existing phase and tail machinery eliminate the resulting
   `-1/-2` cells under the additional unit-remainder hypothesis?

The positive `R` branch remains the logarithmic second-shell inequality from
`FatalBorrowMidpointTransfer.lean`.

## Validation status

Focused Lean validation and the final serialized Lake authority check both
pass.  The three declarations depend only on `propext`, `Classical.choice`,
and `Quot.sound`; none depends on `sorryAx`.
