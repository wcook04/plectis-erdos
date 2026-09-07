# Forbidden-difference eight-of-nine (ordinary candidate)

The eight depth-16 seeds $K(h,12,16)$ for $h=1,\ldots,8$ are already
Lean-checked as `certifiedKill_all_small`.  Type B r3 extracts an
eventual forbidden-difference statement: for every integer $t\ge21$, at
least eight of the nine consecutive tests $K(t+j,12,t+j)$, $j=0,\ldots,8$,
hold.

**Replay.** Exact $(D,\rho,B,\mathrm{margin})$ rows and the $t=21$
threshold $37008/2^{21}<40640/2^{21}$:
`scripts/check_forbidden_difference_eight_seeds.py --quick`.

**Does not prove $S$ irrational.** Eventual success on one ray is
compatible with rationality when the fixed basepoint has not absorbed the
dyadic denominator.  High certificate density at $N=12$ is not
`FullMersenneCanonicalBasepointResidueGapSupply`.

**Evidence class.** Ordinary-proof candidate extracted from existing
seeds and concatenation.  Not in the manuscript.  Isolation remains
undischarged.
