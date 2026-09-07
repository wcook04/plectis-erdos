# Digital height and finite cutoffs for the cylinder rewrite

Status: exact algebraic results and exact counterexamples, 2026-08-20.  The
single-lift cutoff proved below is independent of rewrite order.  The first
cross-cohort example uses two independently labelled first lifts.  A
second-generation instance is reachable from one initial \(M(2,3)\) under a
legal pairwise schedule, but is not asserted to occur under every possible
whole-cohort rule.

Put

\[
 w_r=\frac1{2^r-1},
 \qquad
 M(a,b)=w_aw_b.
\]

## 1. Exact digital height of a power block

For positive integers \(a,b\) and an integer \(j\) with
\(a+b-j\geq1\), direct cross-multiplication gives

\[
\begin{split}
 2^jM(a,b)>w_{a+b-j}
 &\iff
 2^j(2^{a+b-j}-1)>(2^a-1)(2^b-1)\\
 &\iff
 \boxed{2^a+2^b>2^j+1.}                             \tag{1}
\end{split}
\]

Suppose now that \(a,b\geq2\) and \(0\leq j\leq a+b-2\).  There is also the
upper comparison

\[
 2^jM(a,b)<w_{a+b-j-1}.                              \tag{2}
\]

Indeed, (2) is equivalent to

\[
 2^a+2^b<2^{a+b-1}+2^j+1,
\]

and \(2^a+2^b\leq2^{a+b-1}\) for \(a,b\geq2\).  Whenever the condition on
the right of (1) holds, the first Mersenne weight affordable from the power
block \(2^jM(a,b)\) is therefore exactly

\[
 w_{a+b-j}.                                         \tag{3}
\]

This makes

\[
 H(kM(a,b))=a+b-\lfloor\log_2k\rfloor               \tag{4}
\]

an exact first-rank coordinate for the power blocks of a coefficient, rather
than only an estimate of their real size.

## 2. Every single LCM lift has a schedule-independent cutoff

For a collision at stop \(n\), choose an endpoint
\(2\leq e<n-1\), and put

\[
 L=\operatorname{lcm}(e,n-1),
 \qquad
 A=\frac{2^L-1}{2^e-1}
   -\frac{2^L-1}{2^{n-1}-1}.
 \tag{5}
\]

The LCM lift is \(A M(n,L)\).  Since \(e\geq2\),

\[
 0<A<\frac{2^L-1}{2^e-1}
 \leq\frac{2^L-1}{3}<2^{L-1}.                       \tag{6}
\]

It follows that every nonzero binary digit \(2^j\) of \(A\) has
\(j\leq L-2\).  Applying (1) with \(a=n,b=L\) shows that the corresponding
power block has first rank

\[
 n+L-j\geq n+2.                                     \tag{7}
\]

There is a stronger statement which does not depend on splitting \(A\) into
binary blocks.  The exact lift identity gives

\[
 A M(n,L)=M(e,n)-M(n-1,n)
         =w_n(w_e-w_{n-1}).
 \tag{8}
\]

Consequently

\[
 0<A M(n,L)<\frac{w_n}{3}<w_{n+1}.                  \tag{9}
\]

The last inequality holds for \(n\geq4\), which follows from the hypotheses
on \(e\).

Consider any value-preserving rewrite of this single lifted block in which
all atoms and unresolved cylinders have nonnegative coefficients.  No state
of the rewrite can contain an atom \(w_r\) with \(r\leq n+1\), since such an
atom alone is at least \(w_{n+1}\), larger than the total value in (9).
Thus:

\[
 \boxed{\text{Every atom emitted from one isolated LCM lift has rank at
 least }n+2.}                                       \tag{10}
\]

This conclusion is independent of the order in which the block is split,
carried, or otherwise positively normalized.  It applies before one knows
whether the unresolved cylinder mass eventually vanishes.

The ordinary and collision rewrites also increase the effective height of
their cylinder frontier locally.  An ordinary split of a stop-\(n\) cylinder
has child stops \(n+a,n+b\geq n+2\).  In a collision rewrite, the three
ordinary children again have stops at least \(n+2\), while (6) gives

\[
 H(A M(n,L))\geq n+2.                               \tag{11}
\]

After the atom \(w_n\), respectively \(w_{n-1}\), has been removed, every
labelled cylinder produced by either local rule has gained at least two
units of effective height.

## 3. Coalescence can lower effective height

The preceding monotonicity holds for labelled outputs.  It need not survive
when several blocks on the same cylinder are merged.  If
\(k_1,\ldots,k_m\) are positive integers and \(q=\max_i\lfloor\log_2k_i\rfloor\),
then

\[
 \left\lfloor\log_2\sum_{i=1}^m k_i\right\rfloor
 \leq q+\lceil\log_2m\rceil.
 \tag{12}
\]

Hence coalescing \(m\) blocks can lower their effective height by as much as
\(\lceil\log_2m\rceil\).  For two blocks the possible loss is one, and this
loss occurs for the first LCM lift.

At the first collision for \(M(2,3)\), take \(n=11,e=2\).  Then

\[
 L=10,\qquad A=340=2^8+2^6+2^4+2^2.
 \tag{13}
\]

The four power blocks in (13) have first atom ranks

\[
 13,\ 15,\ 17,\ 19.
 \tag{14}
\]

The complete lifted block satisfies

\[
 w_{13}<340M(11,10)<w_{12},                         \tag{15}
\]

in agreement with \(H(340M(11,10))=13\).

Now take two independently labelled copies of the same lift.  Their combined
coefficient is

\[
 680=2^9+2^7+2^5+2^3,
\]

and exact comparison gives

\[
 \boxed{w_{12}<680M(11,10)<w_{11}.}                 \tag{16}
\]

Equation (16) forces rank \(12\) in every Boolean representation of the
combined value.  If all selected ranks were greater than \(12\), strict
superincreasingness would make their total smaller than \(w_{12}\).  On the
other hand, any atom of rank at most \(11\) is already larger than the whole
value in (16).  Therefore \(w_{12}\) must occur.

Each labelled lift separately has the schedule-independent cutoff \(13\)
from (10), but their sum has the forced cutoff \(12\).  Equivalently, the
duplicate first atoms at ranks \(13,15,17,19\) cannot all be cleaned while
preserving the individual cutoff; their carries move one rank to the left.
This is a schedule-independent cross-cohort failure of effective-height
monotonicity.

The same loss is reachable at the next generation from a single initial
cylinder.  The first \(e=2\) lift consists of \(340\) copies of
\(M(11,10)\), all with stop \(21\).  Pair two copies, choose endpoint \(10\),
and apply the LCM rule.  Since

\[
 \operatorname{lcm}(10,20)=20,\qquad
 \frac{2^{20}-1}{2^{10}-1}
 -\frac{2^{20}-1}{2^{20}-1}=1024,
\]

the output block is \(1024M(21,20)\).  Two such pair rewrites create two
identical blocks, and

\[
\begin{split}
 w_{31}&<1024M(21,20)<w_{30},\\
 w_{30}&<2048M(21,20)<w_{29}.
\end{split}                                         \tag{17}
\]

Thus each second-generation lift has cutoff \(31\), while their combined
value forces rank \(30\) under every positive Boolean normalization.  This
configuration is produced whenever the endpoint-\(10\) pair rewrite is used
twice among the \(170\) available pairs.  It is a legal continuation of the
single-root rewrite, although a different whole-cohort rule might avoid this
particular pair of blocks.

## 4. Consequence for a global normal form

For a single collision, the cleaned cylinder frontier has a rigorous
two-rank gain, and the entire LCM block obeys the same cutoff under every
positive schedule.  This is the strongest cutoff statement available from
the digital-height coordinate alone.

It does not give a global confluence theorem.  A global state must retain the
labels of independently created blocks, or record a budget for the logarithmic
loss (12).  Treating equal cylinders as one coefficient can lower the cutoff,
and treating them separately only postpones the same loss until their atom
streams collide.  Since the number of cohorts is not bounded by the local
rewrite, (12) supplies no uniform global cutoff.

The doubled first-lift example is a counterexample for arbitrary finite input
multisets.  Equation (17) additionally shows that the same one-rank loss can
occur along a legal rewrite from one initial \(M(2,3)\).  This disproves the
assertion that effective height is monotone along every legal schedule.  It
does not disprove the existence of a specially chosen confluent schedule.
Such a theorem must use
an ancestry constraint which selects a schedule avoiding unbudgeted
coalescence, or include the logarithmic loss (12) in its global potential.

## 5. Reproduction

Run

    python3 formal_math/erdos257_period_noncollapse/scripts/digital_height_cylinder_cutoff_audit.py \
      --maximum-stop 60 --coefficient-limit 700

The script verifies (1) on the displayed finite parameter range, checks
(5)--(11) for \(1653\) LCM lifts, and gives the exact comparisons
(13)--(17).  The proofs of (1), (6), (9), (10), and (12) are algebraic and
do not depend on these finite checks.
