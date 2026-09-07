# Source-linear coboundary no-go for Erdős #269

## The analytic question

The genuine normalized source tail satisfies

`X_(a+1)=b_a X_a-d_a`,

where the actual radix `b_a` lies in `{2,6,10,30}` and `d_a` is the exact
ordered `{2,3,5}` shell digit.  If some `X_a` is an integer, every later state
is an integer.  Equivalently, the source digit has an integer coboundary

`d_a=b_a C_a-C_(a+1)`

along that tail.  The existing all-scale dichotomy says that excluding this
branch forces cofinal return to distance at least `1/31` from every integer.

The first natural closed-form attempt used one channel-count potential and
failed.  The computation here tests a substantially larger, source-complete
linear version before spending proof effort on it.

## The tested source span

For each prime channel `p in {2,3,5}`, let `e_p(a)` be the largest exponent
with `p^e<=2^a`.  Let

- `W_p(e)` count pairs of powers from the other two channels whose product is
  below `p^e`;
- `A_p(e)=sum_(r<=e) W_p(r)` be its cumulative simplex count.

These are the exact boundary and cumulative count arrays used by the source
digit constructor.  At scale `a` the nine coordinates are

`1, a, a^2, A_2(a), A_3(e_3(a)), A_5(e_5(a)),`

`W_2(a), W_3(e_3(a)), W_5(e_5(a))`.

The candidate potential may use a separate rational linear functional of all
nine coordinates for each current radix phase `2`, `6`, `10`, and `30`.  It
therefore has 36 independent rational coefficients and strictly contains the
single-channel and phase-blind linear proposals.

## Exact obstruction

Substituting the candidate into `d_a=b_a C_a-C_(a+1)` produces a rational
linear system.  The first 26 actual equations are consistent because the
coefficient matrix has not yet exposed the obstruction.  Adding equation 27
gives coefficient rank 26 and augmented rank 27.

The checker does more than compare ranks.  It extracts a primitive integer
left-null vector `lambda` and verifies exactly that

`lambda^T M=0` but `lambda^T d != 0`.

This is a finite exact counterexample to the entire declared functional class,
not a statistical failure or a longer-horizon audit.  It proves that the
actual initial source tail has no phase-conditioned source-linear coboundary
of this form.

The replay receipt makes the certificate numerical rather than merely
qualitative: the first 27 source equations have coefficient rank `26` and
augmented rank `27`, while the primitive left-null vector pairs to zero with
all 36 coefficient columns and to
`476861343184323130448265656627744` with the digit vector.  This is the exact
finite obstruction consumed by the note; it is not a claim about later
windows or about the full nonlinear carry problem.

## Consequence and boundary

This eliminates a structurally distinct integral-tail mechanism: direct
finite-rank linear recombination of every channel coordinate already used to
build the digit.  Any surviving exact integral carry must use nonlinear
information, unbounded phase memory, or begin only after a later state without
extending to the declared global source formula.  The result does not exclude
those possibilities and therefore does not prove irrationality.

That boundary matches `WeightedPhaseCarry.lean`: finite phase residues retain
an uncontrolled transfer coordinate unless an additional reachable-subspace
collapse is proved.  The next useful computation should test a mathematically
specified nonlinear potential or the rank of the actual reachable phase
subspace, not add arbitrary linear features until a prefix interpolates.

Replay:

```sh
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos269_source_linear_coboundary.py
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos269_source_linear_coboundary.py --check
```
