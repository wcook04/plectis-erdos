# No rational target from a one-copy affine rewrite cycle

Put
\[
  w_n=\frac1{2^n-1},\qquad M(a,b)=w_aw_b.
\]
This note tests a genuinely different construction family: choose a rational
target other than \(1/21\), emit a fixed finite Boolean block, and leave one
contracted residual copy in one of finitely many states.  The state and its
rank clock are then iterated.  This attractive family cannot produce a
rational infinite Boolean Mersenne sum.  Additive clocks land in the
machine-checked eventually-periodic case, expanding clocks land in the
machine-checked reciprocal-summable case, and a single cylinder branch
cannot even return projectively to its endpoint type.

The result rules out a precise family, not all finite-state substitutions.
Branching residual systems or automata whose clock is not eventually affine
are outside its scope.

## 1. The one-copy affine-clock model

Consider a deterministic rewrite with finitely many residual states.  At
each step it emits at most \(K\) distinct ranks, leaves exactly one residual
state, and updates an integer clock by
\[
  n\longmapsto c_i n+d_i,\qquad c_i\ge1,\quad d_i\ge0, \tag{1}
\]
where the coefficients and emitted offsets depend only on the current
state.  Assume emitted ranks are Boolean and tend to infinity, and that the
residual value tends to zero.  The finite state path is eventually periodic.
Over one period, the composite clock has the form
\[
  T(n)=cn+d,\qquad c\ge1.                           \tag{2}
\]

If \(c=1\), every multiplier in the period is one.  If \(d=0\), the
automaton revisits only finitely many ranks and cannot emit an infinite
Boolean support.  If \(d>0\), the finite emission pattern repeats after a
fixed translation.  Apart from a finite prefix, support membership is
periodic with a period dividing a multiple of \(d\).  The Lean theorem
`irrational_erdosSupportSeries_eventuallyPeriodic` proves that every infinite
support of this kind has irrational Mersenne sum.

If \(c\ge2\), every clock orbit grows geometrically.  Since only boundedly
many ranks are emitted per stage, the support \(S\) satisfies
\[
  \sum_{n\in S}\frac1n<\infty.                     \tag{3}
\]
The Lean theorem
`irrational_erdosSupportSeries_two_of_summable_reciprocal` proves that every
infinite Boolean support satisfying (3) also has irrational Mersenne sum.

Thus in both cases the putative fixed point
\[
  x=\sum_{n\in S}w_n                                \tag{4}
\]
is irrational.  It cannot equal the rational target from which the rewrite
started.  This applies after any finite prefix, because both cited theorems
are stable under finite support changes.

In particular, a finite Boolean block plus a geometrically shifted copy is
not a possible counterexample mechanism.  Its clean separation of emission
blocks is exactly what makes its reciprocal support summable.  A translated
copy is not a way around the obstruction: finite-state repetition makes its
support eventually periodic instead.

## 2. A cylinder branch has no projective residual cycle

The ordinary positive cylinder split is
\[
  M(a,b)=w_{a+b}+M(a+b,b)+M(a,a+b).                 \tag{5}
\]
Following one residual child applies one of the endpoint matrices
\[
  L=\begin{pmatrix}1&1\\0&1\end{pmatrix},
  \qquad
  R=\begin{pmatrix}1&0\\1&1\end{pmatrix}.          \tag{6}
\]
Every nonempty split word \(W\) has nonnegative integer entries and
\(\det W=1\).  It cannot return a positive endpoint vector
\(v=(a,b)^T\) to an integer dilation of itself.  If
\[
  Wv=kv,\qquad k\in\mathbb N,                      \tag{7}
\]
then the other eigenvalue is \(1/k\).  Since it is a rational algebraic
integer, \(1/k\) must be an integer, so \(k=1\).  But every nonempty word in
\(L,R\) strictly increases \(a+b\), contradicting (7).

Cylinder symmetry does not create a loophole.  Let
\(J=\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)\).  If
\[
  Wv=kJv,                                           \tag{8}
\]
then \(JW\) is an integer matrix of determinant \(-1\) with integer
eigenvalue \(k\).  Its other eigenvalue is \(-1/k\), so the same algebraic-
integer argument gives \(k=1\).  Again (8) is impossible because its two
sides have different coordinate sums.

Therefore no endpoint choice makes a one-branch cylinder split return to
the same unordered cylinder type, even up to dilation.  A finite-state
cycle of such branches reduces to one nonempty product and is equally
impossible.

## 3. Consequence for construction searches

This eliminates three superficially different candidate mechanisms at
once:

1. a residual cycle with a fixed additive rank translation;
2. a finite Boolean block followed by a dilated copy of the same support;
3. a single cylinder residual whose endpoint type repeats after finitely
   many positive splits.

The first is eventually periodic, the second is reciprocal-summable, and
the third has no endpoint cycle.  Changing the rational target does not
alter any of these conclusions.  For example, starting from
\(M(2,5)=1/93\), rather than \(M(2,3)=1/21\), cannot make this automaton
class viable.

Any successful positive construction must therefore retain genuinely
branching residual ownership and generate a support that is simultaneously
non-eventually-periodic and reciprocal-divergent.  Those are not aesthetic
complications: the existing machine-checked theorems force them.

## 4. Reproduction and theorem anchors

The exact theorem anchors are:

- `Erdos257PeriodNoncollapse/CertificateKernel.lean`, theorem
  `irrational_erdosSupportSeries_eventuallyPeriodic`;
- `Erdos257PeriodNoncollapse/ReciprocalSupportIrrationality.lean`, theorem
  `irrational_erdosSupportSeries_two_of_summable_reciprocal`.

The companion script checks determinants and the absence of direct or
swapped projective endpoint returns for all split words through length 10
and positive endpoints through 40.  That finite audit tests the formulas;
the proof above is not based on the cutoff.

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/finite_state_self_similarity_nogo.py
