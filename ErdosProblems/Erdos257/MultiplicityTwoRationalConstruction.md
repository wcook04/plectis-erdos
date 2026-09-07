# A rational Mersenne construction with multiplicity two

Let

\[
 \mathcal A=\left\{\sum_{n\ge1}\frac{b_n}{2^n-1}:b_n\in\{0,1\}\right\},
 \qquad E=\sum_{n\ge1}\frac1{2^n-1}.
\]

The fair-coding result gives \(\operatorname{vol}(\mathcal A)=1\).  Digit
complementation gives the exact symmetry

\[
  \mathcal A=E-\mathcal A.                                  \tag{1}
\]

These two facts construct a concrete rational Mersenne subseries once the
coefficient alphabet is enlarged only from \(\{0,1\}\) to \(\{0,1,2\}\).

## Positive-overlap theorem

> **Theorem.** The convolution of the achievement-set indicator satisfies
> \[
>  (\mathbf1_{\mathcal A}*\mathbf1_{\mathcal A})(3/2)
>  \geq \frac72-2E\geq\frac{11}{42}>0.                       \tag{2}
> \]
> Consequently there are continuum-many pairs \((x,y)\in\mathcal A^2\)
> with \(x+y=3/2\).  Some such pairs have both Boolean supports infinite.
> They may moreover be chosen so that each support has natural density
> \(1/2\), and therefore divergent reciprocal sum.
> More generally, the convolution is positive for every
> \(s\in(26/21,2)\), so every rational in that interval has continuum-many
> such paired representations.

For a general real \(s\), symmetry (1) gives

\[
\begin{aligned}
 (\mathbf1_{\mathcal A}*\mathbf1_{\mathcal A})(s)
 &=\operatorname{vol}(\mathcal A\cap(s-\mathcal A))\\
 &=\operatorname{vol}(\mathcal A\cap(\mathcal A+s-E)).       \tag{3}
\end{aligned}
\]

Put \(t=s-E\).  The two sets in the last intersection both have measure one,
and their union is contained in an interval of length \(E+|t|\).  Therefore

\[
 \operatorname{vol}(\mathcal A\cap(\mathcal A+t))
 \geq 2-E-|t|.                                               \tag{4}
\]

The first four terms give \(E>3/2\).  The standard Mersenne-tail bound gives

\[
 E=1+\frac13+\sum_{n\ge3}\frac1{2^n-1}
 \leq1+\frac13+\frac27=\frac{34}{21}.                        \tag{5}
\]

At \(s=3/2\), equations (4)--(5) yield

\[
 2-E-|3/2-E|=\frac72-2E
 \geq\frac72-\frac{68}{21}=\frac{11}{42},
\]

proving (2).

The same estimate gives the stated interval.  If \(s\leq E\), then (4)--(5)
give

\[
 2-E-|s-E|=2+s-2E\geq s-\frac{26}{21}>0.
\]

If \(s\geq E\), then the lower bound is \(2-s>0\).  Hence every real
\(s\in(26/21,2)\), and in particular every rational there, has positive
convolution mass.

Positive overlap means a positive-measure set of \(x\) satisfies both
\(x\in\mathcal A\) and \(3/2-x\in\mathcal A\).  Strict superincrease gives
each achievement point a unique Boolean coding.  Finite-support points form
a countable set, as do their \(3/2\)-reflections.  Removing those two
countable exceptional sets from a positive-measure overlap leaves pairs for
which both supports are infinite.

Fair Bernoulli coding strengthens this last choice.  By the strong law of
large numbers, the support of almost every bit sequence has natural density
\(1/2\).  The fair-coding pushforward identifies the corresponding full-
measure subset of digit space with a full-Lebesgue-measure subset of
\(\mathcal A\).  Its complement is null.  Translation and reflection preserve
null sets, so the positive overlap in (2) remains positive after removing
points for which either \(x\) or \(3/2-x\) lacks density \(1/2\).  We may thus
choose both supports with density \(1/2\).  In particular,

\[
 \sum_{n:b_n=1}\frac1n=\sum_{n:b'_n=1}\frac1n=\infty.        \tag{5a}
\]

The construction therefore lives on both sides inside the unresolved
reciprocal-divergent regime; it is not an artifact of the already-solved
reciprocal-summable class.

## The resulting rational coefficient sequence

Choose such a pair and write

\[
 x=\sum_n\frac{b_n}{2^n-1},\qquad
 y=\sum_n\frac{b'_n}{2^n-1}.
\]

Then \(c_n=b_n+b'_n\in\{0,1,2\}\), the support of \(c\) is infinite, and

\[
 \boxed{\sum_{n\ge1}\frac{c_n}{2^n-1}=\frac32.}              \tag{6}
\]

For the density-half choice, the Cesàro mean of the multiplicity sequence is
also exact:

\[
 \lim_{N\to\infty}\frac1N\sum_{n\leq N}c_n=1.               \tag{7}
\]

This is stronger than a signed Lambert identity: every coefficient is
nonnegative, the multiplicity ceiling is two, and the construction is backed
by a positive-measure family of Boolean pairs rather than one formal
cancellation sequence.

It is not yet a counterexample to Erdős 257.  Equation (6) does not imply that
either Boolean half \(b\) or \(b'\) has rational value.  Turning one of these
paired representations into a single rational Boolean support is precisely a
global multiplicity-two Booleanisation problem.

## Interaction with the existing renormalisation no-go

[`MultiplicityRenormalisationAttack.md`](MultiplicityRenormalisationAttack.md)
shows why the obvious local carry cannot finish the job:

\[
 2w_d=w_{d-1}-\frac1{(2^{d-1}-1)(2^d-1)}.
\]

The first nontrivial positive defect is already \(1/21\).  The new theorem
therefore changes the input side of that mechanism—an infinite rational
multiplicity-two sequence now exists unconditionally—but it does not evade
the global defect boundary.  A successful next move must exploit correlations
between the two Boolean codings supplied by the overlap, not apply the same
atomwise carry independently.

[`RationalFiberCorrelationAudit.md`](RationalFiberCorrelationAudit.md) tests
that correlation directly.  Through rank (512), the retained (3/2)-fibre
prefixes have tail joint frequencies essentially
((p_{00},p_{01},p_{10},p_{11})=(1/4,1/4,1/4,1/4)), with about (N/4)
double-used coordinates rather than a sparse collision set.  This finite
diagnostic closes generic-fibre selection plus sparse cleanup as a mechanism;
it leaves an exceptional, globally anti-correlated fibre point as exactly the
Boolean target still requiring construction.

## Exact computational audit

[`scripts/multiplicity_two_rational_overlap_audit.py`](scripts/multiplicity_two_rational_overlap_audit.py)
checks all rational constants in (2)--(5) using `Fraction`.  It also enumerates
bounded prefix pairs in the necessary two-copy outer-tail corridor.  Those
cylinder rows map the finite geometry only; the proof of (6) is the all-scale
measure argument above.

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/scripts/multiplicity_two_rational_overlap_audit.py
```

The durable receipt is
`state/formal_math/erdos257_period_noncollapse/multiplicity_two_rational_overlap_receipt.json`.

Claim boundary: this proves a rational infinite \(\{0,1,2\}\)-coefficient
Mersenne series and continuum-many paired Boolean realizations.  It proves no
rational \(\{0,1\}\)-coefficient series and does not settle Erdős 257.
