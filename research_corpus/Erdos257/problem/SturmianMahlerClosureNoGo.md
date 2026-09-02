# Sturmian infinite tower: finite polynomial Mahler closure is absent

This is a problem-directed elimination, not a new focus.  The programme target
remains Erdős 257.  The disposable probe asks whether the first unsolved
positive-density model class—quadratic Sturmian supports—collapses the whole
Lambert tower to finitely many ordinary Sturmian generating-function values.

For the characteristic word `a_n` put

\[
H(x)=\sum_{n\geq0}a_nx^n,
\qquad
L(1/2)=\sum_{r\geq1}H(2^{-r}).
\]

The direct sparse-shift transfer was already eliminated in
`SturmianHeckeLambertTransfer.md`.  A remaining elementary possibility was a
finite polynomial 2-Mahler closure

\[
\sum_{j=0}^{J}P_j(x)H(x^{2^j})=Q(x).             \tag{1}
\]

Such a relation could reduce the dependent evaluations in the Lambert tower
to a finite system before applying a value theorem.  The exact verifier
`scripts/sturmian_mahler_closure_probe.py` constructs the coefficient matrix
of (1) above `deg Q`.  Its entries are zero or one.  Full column rank over
`F_2` therefore proves full column rank over `Q` and excludes every rational
polynomial relation in the audited box, independently of coefficient height.

## Exact result

For each of the characteristic words of slopes

- `(sqrt(5)-1)/2`,
- `sqrt(2)-1`, and
- `sqrt(3)-1`,

the matrix has full rank for 13 tower levels (`j=0,...,12`) and
`deg P_j <= 1024`: 13,325 independent columns.  Full rank is reached after
13,325--13,327 coefficient rows depending on the slope.  The bits are produced
by exact integer-square-root floor differences, so there is no floating-point
classification boundary.

## Consequence and stop condition

The bounded finite polynomial-Mahler closure mechanism is eliminated on three
structurally different quadratic Sturmian controls.  Increasing the same
degree/level box is now a horizon audit and should not receive more allocation.
A Sturmian construction remains meaningful only if it supplies one of:

1. a genuinely infinite-tower identity;
2. a nonlinear relation coupling the values `H(2^-r)`;
3. a value theorem for the Lambert--Sturmian double sum itself.

The available primary results treat ordinary Sturmian coefficient series or
finite collections of their values, not this double sum: see
[Bugeaud--Laurent](https://arxiv.org/abs/2203.12901) and
[Luca--Ouaknine--Worrell](https://arxiv.org/abs/2204.08268).  Therefore this
receipt is an exact finite no-go, not an irrationality theorem for the
Sturmian Lambert value and not a solution of Erdős 257.
