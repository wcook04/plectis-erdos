# Failure map: which information is missing?

## 1. Individual actual returns do not imply a common return

Insufficient information: each of two supports has arbitrarily small displacements, even along multiples of every fixed integer.

Exact falsifier: research Theorem 5.3 partitions the primes into two reciprocal-divergent supports with precisely that property, while the sum of their displacements is greater than 1/3 everywhere.

Stronger information that works: the accepted r5 estimate bounds both nonnegative tests under the same finite distribution. This remains substantive after strengthening the counterexample from abstract functions to actual supports.

## 2. Countable component certificates need a tail budget

Insufficient information: every member of a countable family belongs to the finite mixed class.

The untruncated union can be all primes, even when each member is a singleton. More strongly, the two-colour example fails already for two individual-return supports.

What works for construction: freeze the finite union, choose its return N, and start all later components after R with R-N large. The exact residual contribution is at most `2^(N+1-R)`. The delayed-gluing theorem preserves all but finitely many elements of every input host. For the prescribed untruncated union, one still needs compatible times and `2^N X_residual -> 0`.

## 3. Failure of one displayed cover is not a separation theorem

Insufficient information: the cost of the author's chosen covering decomposition diverges.

The repair: use the cover-independent logarithmic moment, and then prove its stability under reciprocal-summable erasure. On a centre missed by the finite prime set, every weighted term costs exactly `1/a`. A finite weighted budget cannot remove the entire unbounded logarithmic obstruction. This rules out all alternative decompositions. The distinct-centre host is the application.

The next question is the converse direction. Does a bounded logarithmic gauge produce a positive divisor cover under a natural structural condition? The exact cube calculation supplies asymptotic duality on that family, but no unrestricted representation theorem.

## 4. Generic hereditary irrationality does not determine a rational target

Insufficient information: return-admissible hosts form a dense G_delta, and almost every host in the sense of Baire category has the hereditary all-base conclusion.

Missing information: the actual greedy divisor pulses of the distinguished target. The r6 construction chooses future coefficients and colours. The greedy support of 1/2 or 1/21 does not offer that freedom. Its unproved inequality remains `c_x(N+1) >= Q_N + beta_N` cofinally.

The generic hereditary value conclusion itself is also accessible from strict-tail injectivity and countability of rational values. The additional object studied here is the arithmetic return certificate. The word “generic” must specify its topology or probability model. No conversion from a residual class into a probability-one statement has been made here.

## 5. Positive-return improvements cannot cover prime-core supports

Exact boundary already accepted: Delta_P(N)>1/3 for every positive shift. The full prime series is nevertheless irrational by Tao–Teräväinen, Theorem 1.3.

Further refinement of this positive-return functional cannot settle that regime. The relevant analytic inputs must detect a different feature, such as simultaneous weighted correlations or a phase obstruction. The r6 prime partition makes the boundary visible without any synthetic recurrence.

## 6. Denominator lower bounds point in the wrong direction for the naive tail argument

A nonzero rational difference obeys `|p/q-N/D| >= 1/(qD)`. A lower bound on D weakens that inequality. The signed finite-period theorem supplies a reusable valuation invariant, but not the upper height control needed for this approximation argument.

## 7. A cross-problem construction principle, with different outcomes

The #251 source `SparseRationalisationCore.lean` has an exact capacity telescope and a variable-digit remainder invariant. Both it and delayed gluing preserve finite constraints by reserving an explicit tail capacity. In #251, free digits are used to rationalise a series while retaining coarse constraints. In #257, positive displacements and a fixed lattice are used to force irrationality for a constructed host. This demonstrates the importance of which coefficients remain free; it is not a reduction between the two parent problems.
