# Polynomial coupling before the rank-one quotient (ordinary candidate)

Type B r3 proposed, for nonnegative-coefficient $P$ with $P(1)=1$ and
$Y\ge4$,
\[
 \mathcal Q_Y(P)\ge Q(1,Y)+\frac{1-a_1}{50}.
\]
This is coupling *before* the quotient, not a positive average of the
already-checked monomial numbers $Q(e,Y)$.

**Countermodels (necessary).** A constant term $P=1$ gives
$\mathcal Q_Y=T_Y(2)$, so no uniform positive floor.  The signed interpolant
$P_Y(x)=1-\prod_{d\le Y}(1-x/x_d)$ takes the value $1$ at every atom and
again yields $T_Y(2)$.  Nonnegative coefficients, not atom-positivity, are
essential.

**Checked here.** Exact constants
$\delta=2627/48020$, derivative $1247825/56205009>1/50$, $Q(1,5)=q_*$,
and both countermodels:
`scripts/check_polynomial_rank_one_coupling_floor.py --quick`.
The interpolation derivative inequality for every such $P$ is not
re-proved by the script.

**Evidence class.** Ordinary-proof candidate.  Not in the manuscript.
Does not decide $S$.  Does not close `theta_two_denominator_compression`.
