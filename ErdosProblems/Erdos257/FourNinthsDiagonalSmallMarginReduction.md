# The four-ninths diagonal: a sharp small-margin reduction

## Status

This note does not solve Erdős Problem 257.  It records a new exact
contraction of the remaining (4/9) construction problem and separates the
Lean-checked arithmetic from the analytic conclusion that is still
conditional.

Let

\[
 u_d\in\{0,1,3\},\qquad
 A_d=2\sum_{\substack{a<d\\a\mid 2d-1}}b_a+
       \sum_{\substack{a<d\\a\mid 2d}}b_a,
\]

and put

\[
 T_d=4\rho_{d-1}+u_d-A_d,\qquad
 b_d={\bf 1}_{T_d\geq 2^d+1},\qquad
 \rho_d=T_d-b_d(2^d+1).
\]

The executable Lean definition reproduces

\[
 b_1\ldots b_{12}=010110110001,
 \qquad \rho_{12}=2460.
\]

In particular (b_1=0) and (b_2=b_4=b_{12}=1).

## The paired-load bound

Write (s_{d-1}=\sum_{a<d}b_a).  Since (2d-1) and (2d) are
coprime, an index (a\geq2) cannot divide both.  Its coefficient in (A_d)
is therefore at most two.  The only common divisor is (a=1), and its bit is
zero.  Hence

\[
 \boxed{A_d\leq 2s_{d-1}.}
\tag{1}
\]

This improves the coefficient-three selected-count estimate used in the
earlier finite-injury analysis.

Suppose the step at (d) is skipped and nevertheless crosses below zero.
Then

\[
 4\rho_{d-1}+u_d-A_d<0.
\]

As (u_d\geq0), (1) gives the sharp necessary condition

\[
\boxed{2\rho_{d-1}<s_{d-1}.}
\tag{2}
\]

Thus a large divisor load is not by itself a failure mechanism.  The orbit
must first enter the strip below half of its total selected count.
The source-current Lean theorem
`fourNinthsDiagonalState_negative_successor_forces_halfSelectedMargin`
now applies this conclusion directly to the executable diagonal state: a
negative successor is necessarily a skipped step and has the margin in (2).
It still does not exclude that margin at all depths.

There is also a last-selection form.  If (j<d) is the last selected rank
before a first negative remainder, every intervening step is skipped and

\[
 \rho_d
 \geq 4^{d-j}\rho_j
   -2s_j\sum_{k=0}^{d-j-1}4^k.
\]

Consequently

\[
 \boxed{3\rho_j<2s_j.}
\tag{3}
\]

Any first negative escape is therefore charged to a selected
two-thirds-small-margin event.  This is a global reduction, not an exclusion
of that event: the predecessor remainder must still be related to the full
Boolean divisor ancestry.

The coarser divisor estimate

\[
 A_d\leq2\tau(2d-1)+\tau(2d)
\]

also shows that an immediate negative crossing is possible only from a
sub-square-root-scale integer remainder.  Finite computation is consistent
with a much larger margin, but it does not prove an all-depth lower bound.

## Positive final boundary

The Lean module also checks the arithmetic core of the positive-fatal
argument.  A final upward dyadic-boundary crossing must have phase
(d\equiv4\pmod6).  In that phase the forced ranks (2,4,12) contribute

\[
 \frac13+\frac1{15}+\frac{256}{4095}
 =\frac49+\frac{74}{4095}>\frac49
\]

to the fractional resolvent.  This contradicts any simultaneously supplied
upper resolvent bound below (4/9).  The Lean theorem deliberately takes the
analytic lower and upper resolvent bounds as hypotheses; it does not claim
that the full no-positive-fatal theorem or diagonal nonnegativity has been
formalized.

## Two tempting completions that do not close the problem

1. Flipping the last selected small-margin bit after a negative injury does
   not by itself give a compactness proof.  The repaired prefix can place
   (4/9) in the adjacent gap between one Mersenne cylinder and the next.
   Excluding that gap is another form of the same ancestry--boundary problem.

2. Kovač and Tao prove that a multiset formed from several Lambert bases can
   have a rational infinite subsum.  Taking the bases to be powers of two does
   not immediately solve Problem 257.  The base (2) contributes exactly the
   critical tail ratio one; the strict tail surplus in their theorem comes
   from repeated exponents supplied by the additional bases.  Removing those
   repetitions removes the surplus that creates the interval of subsums.

The relevant source is V. Kovač and T. Tao,
[On several irrationality problems for Ahmes series](https://arxiv.org/abs/2406.17593),
Theorem 2.3 and its proof.

## Exact remaining producer

The (4/9) disproof route still closes if one proves

\[
 \rho_d\geq0\qquad(d\geq0).
\]

After (1)--(3), a counterexample cannot arise from an ordinary large load.  It
must align a globally reachable selected small margin with the later divisor
ancestry strongly enough to enter (2).  A proof excluding that alignment, or
a different construction of an infinite Boolean support of rational value,
would settle Erdős 257.  Neither is proved here.

## Formal authority

The Lean source is
`Erdos257PeriodNoncollapse/FourNinthsDiagonalNoPositiveFatal.lean`.
The foundational reduction was landed at commits
`1b263c48dade6e73cf20f57b8f4517aff78ae4e0` and
`6bdd20954ffcea8de922838b5264c3174837725d`; the direct concrete bridge below
is source-current private work, checked locally but not a public release.  The
principal declarations are:

- `fourNinthsDiagonalState_twelve`;
- `fourNinths_finalBoundary_phase`;
- `fourNinths_no_positive_fatal_anchor_contradiction`;
- `fourNinthsRankLoad_le_two`;
- `fourNinthsAbstractDiagonalLoad_le_two_selected`;
- `fourNinths_negative_skip_forces_halfSelectedMargin_of_rankBits`;
- `fourNinths_negative_skipBlock_forces_twoThirdsSelectedMargin`.
- `fourNinthsDiagonalState_negative_successor_forces_halfSelectedMargin`.

The focused Lake build and its serialized authority check both exit zero.  The
last-selection inequality (3) is now also checked in its abstract geometric
block form; connecting its weighted-debt hypothesis to the displayed exact
recurrence is the elementary iteration written above.
