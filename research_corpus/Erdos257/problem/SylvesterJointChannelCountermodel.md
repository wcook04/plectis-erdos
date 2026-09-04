# A dense rational countermodel to finite joint-channel arguments

The primitive-prime attack on

\[
\sum_{n\in A}\frac1{2^n-1}
\]

produces exact information about many rational-tail denominators.  One might hope that sufficiently many simultaneous channels, coupled across cutoffs and combined with rapid real decay, force a contradiction.  The construction below shows that this proof architecture is insufficient by itself.  It gives a positive unit-fraction series with density-one index support and rational sum in which **every** fresh prime-power channel from the prefix persists simultaneously in the tail denominator.

This is a countermodel to the local architecture, not a counterexample to the Mersenne statement: its denominators are not (2^n-1).  Its purpose is to identify exactly which Mersenne-specific structure a successful proof must still use.

## 1. The construction

Define the Sylvester sequence by

\[
q_1=2,
\qquad
q_{n+1}=q_n(q_n-1)+1.
\tag{1}
\]

Let

\[
P_N=\prod_{j=1}^Nq_j.
\]

### Lemma 1 (product recurrence)

For every (N\ge1),

\[
q_{N+1}-1=P_N.
\tag{2}
\]

### Proof

For (N=1), both sides equal (2).  If (q_N-1=P_{N-1}), then (1) gives

\[
q_{N+1}-1=q_N(q_N-1)=q_NP_{N-1}=P_N.
\]

∎

Equation (2) also shows that the (q_n) are pairwise coprime.  Indeed, if (i<j), then (q_i\mid P_{j-1}=q_j-1), and hence (q_j\equiv1\pmod{q_i}).

## 2. Rationality and exact tails

From (1),

\[
\frac1{q_n}
=
\frac1{q_n-1}-\frac1{q_{n+1}-1}.
\tag{3}
\]

Therefore the series telescopes:

\[
\sum_{n=1}^N\frac1{q_n}
=1-\frac1{q_{N+1}-1}
=1-\frac1{P_N}.
\tag{4}
\]

Consequently,

\[
\sum_{n=1}^{\infty}\frac1{q_n}=1,
\qquad
\tau_N:=\sum_{n>N}\frac1{q_n}=\frac1{P_N}.
\tag{5}
\]

The support in the index variable is all of (mathbf N).  It has natural density (1), and

\[
\sum_{n\in A}\frac1n=\sum_{n\ge1}\frac1n=\infty.
\]

Thus reciprocal divergence of the support is present in its strongest possible form.

## 3. All prime-power channels persist simultaneously

Fix (i\le N), let (p\mid q_i), and put (mu=v_p(q_i)).  Pairwise coprimality gives (p\nmid q_j) for every (j\ne i).  Yet (5) gives the exact tail valuation

\[
v_p(\tau_N)=-v_p(P_N)=-\mu.
\tag{6}
\]

This holds simultaneously for every prime power in every (q_i) with (i\le N).  In fact,

\[
\operatorname{den}(\tau_N)
=P_N
=\prod_{i=1}^Nq_i.
\tag{7}
\]

This is stronger than selecting one primitive prime from each Mersenne denominator: the entire pairwise-coprime denominator of every prefix term survives in the reduced tail denominator.

There is also no hidden same-prime branching.  For (p\mid q_i), every individual later summand (1/q_j), (j>N\ge i), is (p)-integral.  Nevertheless, their real infinite sum has valuation (-mu).  This is the exact boundary failure that obstructs passage from real convergence to (p)-adic integrality.

## 4. Exact cross-cutoff coupling

For (M<N), equations (5) and (7) give

\[
\tau_M-\tau_N
=\sum_{j=M+1}^N\frac1{q_j},
\tag{8}
\]

and the stronger multiplicative law

\[
\tau_N
=\frac{\tau_M}{\prod_{j=M+1}^Nq_j}.
\tag{9}
\]

In particular,

\[
\tau_{N-1}-\tau_N=\frac1{q_N},
\qquad
\tau_N=\frac{\tau_{N-1}}{q_N}.
\tag{10}
\]

Thus the countermodel does not merely realize each prime channel separately.  It couples all of them through an exact rational recurrence across every pair of cutoffs.

## 5. Real decay does not help

The tails decay faster than geometrically.  From (1),

\[
q_{n+1}=q_n^2-q_n+1\ge\frac12q_n^2,
\]

so (q_n), (P_N), and (1/\tau_N) grow doubly exponentially in the index up to harmless constants.  Hence this model combines:

- positive terms;
- rational total sum;
- density-one, reciprocal-divergent index support;
- arbitrarily many independent fresh prime-power channels;
- exact simultaneous channel persistence in every tail denominator;
- exact cross-cutoff additive and multiplicative laws;
- superexponential real tail decay.

All seven properties coexist without contradiction.

## 6. Separation theorem for the proof architecture

Any proposed contradiction that uses only the seven properties above is invalid: the Sylvester series is an explicit model of all of them with rational sum (1).  In particular, none of the following can suffice, separately or jointly:

1. counting fresh primitive channels;
2. multiplying their forced prime powers into a tail-denominator lower bound;
3. following those valuations through finitely or infinitely many cutoffs;
4. using reciprocal divergence or positive density of the support;
5. combining denominator growth with rapid real decay.

A successful argument for Mersenne reciprocals must use a relation absent from this model.  The available candidates are genuinely Mersenne-specific:

- the divisibility lattice
  \[
  M_a\mid M_b\quad\Longleftrightarrow\quad a\mid b;
  \]
- the simultaneous occurrence of old and new cyclotomic factors inside (M_{ak});
- an exact relation between the real tail and that divisor lattice which cannot be reproduced by a telescoping Egyptian fraction.

The construction therefore gives a decisive joint-channel no-go result.  It does not say that cross-cutoff information is useless.  It says that cross-cutoff information must couple *different Mersenne divisor levels*, rather than merely record the accumulation of independent prime powers in rational tail denominators.
