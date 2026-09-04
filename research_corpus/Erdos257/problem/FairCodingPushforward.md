# Fair coding is Lebesgue measure on the Mersenne achievement set

Put

\[
  w_n=\frac1{2^n-1},\qquad
  \pi(b)=\sum_{n\geq1}b_nw_n,qquad b\in\{0,1\}^{\mathbb N_{>0}},
\]

and let \(\mathcal A=\pi(\{0,1\}^{\mathbb N_{>0}})\).  Give the digit
space the fair Bernoulli product probability \(\mathbb P\).  This note proves
the target-free identity

\[
  \boxed{\ \pi_*\mathbb P=\operatorname{Leb}\!\restriction_{\mathcal A}.\ }
  \tag{1}
\]

The restriction on the right is already a probability measure because the
Lean-checked theorem `volume_mersenneAchievementSet` says
\(\operatorname{Leb}(\mathcal A)=1\).

## Proof

The series defining \(\pi\) converges uniformly, so \(\pi\) is continuous.
The strict tail inequality

\[
  w_n>\sum_{k>n}w_k                                           \tag{2}
\]

makes it injective: at the first unequal digit, that digit's weight strictly
dominates every possible later discrepancy.  This is the content of the
Lean-checked `positiveMersenneDigitValue_injective`.  A continuous bijection
from the compact digit space onto the Hausdorff space \(\mathcal A\) is a
homeomorphism.

Fix a word \(u\in\{0,1\}^n\), let \([u]\) be its digit cylinder, and write

\[
  s_u=\sum_{j=1}^n u_jw_j,qquad
  K^{(n)}=\left\{\sum_{j>n}b_jw_j:b_j\in\{0,1\}\right\}.
\]

Then exactly

\[
  \pi([u])=s_u+K^{(n)}.                                      \tag{3}
\]

All \(2^n\) sets in (3) are translates of the same compact set.  They are
pairwise disjoint by (2), and their union is \(\mathcal A\).  Translation
invariance and finite additivity of Lebesgue measure therefore give

\[
  1=\operatorname{Leb}(\mathcal A)
   =\sum_{u\in\{0,1\}^n}\operatorname{Leb}(\pi([u]))
   =2^n\operatorname{Leb}(K^{(n)}).
\]

Consequently

\[
  \operatorname{Leb}(\pi([u]))=2^{-n}=\mathbb P([u])          \tag{4}
\]

for every finite word \(u\).  The image cylinders form a clopen basis of
\(\mathcal A\), because \(\pi\) is a homeomorphism.  Equality (4) on this
generating pi-system determines the two Borel probability measures on
\(\mathcal A\).  Both measures vanish off \(\mathcal A\), proving (1).

## What this opens

Lebesgue-typical points of \(\mathcal A\) now have genuinely independent fair
support digits, not merely an observed density near one half.  In particular,
the strong law, normality statements, cylinder frequencies, and Bernoulli
mixing transfer verbatim through \(\pi\).  Computations comparing rational
greedy supports with a fair-bit null therefore have an exact reference measure.

This is not a rational-point theorem.  The rationals are a null countable set,
so (1) neither places a rational in \(\mathcal A\) nor excludes one.  Any use
for Erdős 257 must add arithmetic information about exceptional points; the
metric theorem supplies the correct baseline and no more.

## Exact audit

[`scripts/fair_coding_pushforward_audit.py`](scripts/fair_coding_pushforward_audit.py)
uses `Fraction` arithmetic to certify the strict finite-cylinder separations,
the exact monotone stage-volume recurrence, and directed tail brackets through
the requested depth.  Its default run is

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/scripts/fair_coding_pushforward_audit.py
```

and writes
`state/formal_math/erdos257_period_noncollapse/fair_coding_pushforward_receipt.json`.
The finite audit is evidence for the geometry; the all-scale proof is the
argument above, whose two nontrivial inputs—measure one and injective coding—are
already Lean checked.
