# Seam-stall fresh loads do not come from diagonal small margins

## Exact elimination

This computation tests and eliminates one proposed bridge between the two
surviving `4/9` mechanisms.  It does not exclude either mechanism at all
depths, construct an infinite support, or resolve Erdős 257.

The seam computation found that the worst no-strip stall is financed by `88`
distinct selected divisors.  The diagonal reduction independently says that
a first negative diagonal injury must descend from a selected state with

\[
  3\rho_d<2s_d,
\]

where `s_d` is the number of selected ranks.  A tempting unification was that
the seam's fresh contributors were themselves selected at those rare
two-thirds-small-margin events.

The producer reconstructs the exact integer diagonal through rank `146,794`,
which covers every contributor to the worst seam stall, and checks their
selection states.  The result is unambiguous:

- all `88` seam contributors are selected diagonal bits;
- none is selected with `3*rho < 2*s`;
- there are no selected two-thirds-small-margin events anywhere through the
  entire audited diagonal range;
- among the `88` contributors, the largest dyadic leading-zero count of the
  post-selection remainder is only `5` (rank `314`);
- `37` contributors have zero leading-zero deficit, `24` have one, `19` have
  two, and only `8` have three or more.

Thus the fresh contributors are ordinary positive-margin selections.  They
do not inherit the diagonal negative-injury theorem's scarce small-margin
charge.  Treating the two obstructions as one would be an invalid shortcut.

The broader diagonal computation has its own rare near-boundary event—leading
zero count `19` at rank `90,374`—but it still lies exponentially above the
linear selected-count strip and is not a seam contributor.  This confirms
that dyadic closeness and the `3*rho<2*s` injury margin are very different
scales.

## Consequence for the search

The seam route still needs a history-dependent budget on fresh contributors,
but that budget cannot be the existing diagonal small-margin reserve.  The
next useful charges must instead use one of:

1. fixation/extraction geometry when a contributor bit became common to the
   whole cylinder;
2. co-divisor diagonals `q=m/d`, which organize large one-use contributors;
3. a global resolvent or selection-density budget preserved by reachability.

This is a structurally distinct negative result: it prevents the current
formal diagonal theorem from being misapplied to the seam producer and forces
the proof search onto a genuinely new resource.

## Reproduction

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/four_ninths_stall_diagonal_charge.py
./repo-python formal_math/erdos257_period_noncollapse/scripts/four_ninths_stall_diagonal_charge.py --check-receipt state/formal_math/erdos257_period_noncollapse/four_ninths_stall_diagonal_charge_receipt.json
```
