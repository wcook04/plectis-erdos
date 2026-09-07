# Buffered quotient control has no second tempered branch

Status: theorem-level obstruction, 2026-08-21.  The argument is infinite and
does not depend on a computation.  It does not prove Erdős 257 and it does
not exclude searching for a different rational target.  It proves that, for
any fixed target word, a buffered quotient controller has at most one
tempered Boolean trajectory.  Every first wrong Boolean choice survives as a
nonzero homogeneous carry mode.

## 1. Same-forcing carry comparison

For a normalized Boolean support \(A\subseteq\mathbb N_{>0}\), put

\[
 f_A(n)=\#\{d\in A:d\mid n\},
 \qquad
 S(A)=\sum_{d\in A}\frac1{2^d-1}.
\]

Let \(t_n\) be any fixed integer forcing word.  Suppose two Boolean supports
\(A,B\) and two integer carries \(q,r\) satisfy, for every \(n\geq1\),

\[
 \begin{aligned}
 f_A(n)&=2q_{n-1}+t_n-q_n,\\
 f_B(n)&=2r_{n-1}+t_n-r_n,
 \end{aligned}                                      \tag{1}
\]

with \(q_0=r_0\).  No periodicity, boundedness, or sign hypothesis on
\(t,q,r\) is needed for the following identity.  Put
\(\Delta_n=q_n-r_n\).  Subtracting the two rows of (1), multiplying by
\(2^{-n}\), and summing gives the exact finite telescope

\[
 \sum_{n=1}^{N}\frac{f_A(n)-f_B(n)}{2^n}
   =-\frac{\Delta_N}{2^N}.                         \tag{2}
\]

The Lambert regrouping already proved in the corpus gives

\[
 \sum_{n\geq1}\frac{f_A(n)}{2^n}=S(A),
 \qquad
 \sum_{n\geq1}\frac{f_B(n)}{2^n}=S(B).
\]

Passing to the limit in (2) therefore yields the exact boundary-amplitude
law

\[
 \boxed{
   \lim_{N\to\infty}\frac{q_N-r_N}{2^N}=S(B)-S(A).
 }                                                   \tag{3}
\]

The convergence on the left is a conclusion, not an extra hypothesis.  It
follows from convergence of the two nonnegative Lambert series.

## 2. Tempered uniqueness

Assume now that both carries are tempered:

\[
 \frac{q_N}{2^N}\longrightarrow0,
 \qquad
 \frac{r_N}{2^N}\longrightarrow0.                 \tag{4}
\]

Equation (3) gives \(S(A)=S(B)\).  Strict superincreasingness of the
Mersenne weights makes normalized support coding injective, so \(A=B\).
Then \(f_A=f_B\), and (1) gives
\(\Delta_n=2\Delta_{n-1}\).  Since \(\Delta_0=0\), induction gives
\(q=r\).  Thus:

> **Buffered-carry uniqueness theorem.**  For a fixed forcing word and a
> fixed initial carry, there is at most one tempered Boolean divisor-carry
> trajectory.

This is stronger than an eventual-periodic or bounded-carry no-go.  The
forcing word can be arbitrary and the carries can be unbounded; only the
actual boundary condition \(o(2^N)\) is used.

## 3. A wrong buffer creates a quantitatively nonzero escape mode

Suppose \(m\) is the first rank at which \(A\) and \(B\) differ, with
\(m\in A\) and \(m\notin B\).  The strict Mersenne gap gives

\[
 S(A)-S(B)
 \geq \frac1{2^m-1}
      -\sum_{n>m}\frac1{2^n-1}
 =:g_m>0.                                           \tag{5}
\]

Indeed, the most favourable possible repair gives every later rank to
\(B\) and none to \(A\), and even that complete tail is too small.  Combining
(3) and (5),

\[
 \lim_{N\to\infty}\frac{q_N-r_N}{2^N}
 \leq-g_m<0.                                       \tag{6}
\]

With the opposite first choice the inequality reverses.  Hence every first
wrong Boolean decision creates an exponential carry separation whose
normalized amplitude is exactly the resulting Mersenne-value error and whose
absolute amplitude is at least \(g_m\).  Later buffered choices cannot pay it
back.

This identifies the common mechanism behind two descriptions that otherwise
look different:

* in real-greedy coordinates, (5) is the fatal Mersenne hole;
* in quotient coordinates, (6) is the non-tempered homogeneous carry mode.

They are the same irreversible first-bit error measured on opposite sides of
the Lambert transform.

## 4. Consequence for construction searches

The recurrence

\[
 f_b(n)=2q_{n-1}+t_n-q_n
\]

does not provide genuine policy freedom once temperedness is required.  A
controller may temporarily choose between taking a Boolean bit and storing a
unit in the carry, but at most one of those branches can have a tempered
completion.  In particular, repairing the minimal quotient-greedy failures
for \(1/21\), \(1/465\), or another rational target by trying alternative
buffers is not a new construction mechanism: a successful branch must be
the unique real-greedy support of that target.

This does not make quotient coordinates useless.  They can still prove that
the unique branch is tempered, or discover a target for which an arithmetic
law forces that boundary condition.  What they cannot do is evade the real
greedy wall by selecting a different Boolean branch.  Any proposed quotient
policy must therefore prove one of the following genuinely global facts:

1. its choices agree with the target's real-greedy choices at every rank and
   its carry is tempered; or
2. directly, that the homogeneous amplitude in (3) is zero.

Finite nonnegativity, a bounded lookahead, or a locally affordable buffer is
insufficient unless it controls that amplitude.

## 5. Existing formal anchors

The proof uses two current machine-checked inputs:

* `erdosSupportSeries_two_eq_binaryCoeffSeries` in
  `Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean`, for the Lambert
  regrouping; and
* `erdosSupportSeries_two_injective_normalized` together with
  `mersenneTail_lt_weight` in
  `Erdos257PeriodNoncollapse/GreedyAchievementSet.lean`, for strict Boolean
  support injectivity and the positive first-difference gap.

Equation (2) is elementary finite telescoping.  Thus the obstruction is not a
finite search result and does not depend on any unproved socket.
