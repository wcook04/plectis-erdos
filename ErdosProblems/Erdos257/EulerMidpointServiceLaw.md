# The Euler midpoint service law

## 1. What the computation was asked to discover

The goal is not to settle Erdős problem 257 by checking a long prefix.  The
goal is to make the two-million-rank denominator-21 orbit disclose the exact
inequality an all-depth proof would need.

The current shortest analytic route is the doubling running-maximum law

\[
 H(2d)\leq 2H(d),\qquad
 H(d):=1+\max_{0\leq k<d}Q_k.                    \tag{DRMH}
\]

It already implies a linear defect bound, hence the existing Lean-checked
membership endpoint for \(1/21\).  The problem is that `(DRMH)` still looks
like a global comparison between two long histories.  The experiment below
collapses it to the service delivered by one completely determined divisor
layer at a record midpoint.

## 2. The exact midpoint algebra

Let \(b_n\in\{0,1\}\) be the actual greedy support, let \(t_n\) be the binary
digits of the target, and put

\[
 f(n):=\sum_{a\mid n}b_a,
 \qquad
 Q_n=2Q_{n-1}+t_n-f(n).
\]

Suppose a strict defect record occurs at \(n=2d-1\).  Write

\[
 R:=Q_{2d-1},qquad
 g_d:=f(2d)-f(d).
\]

The number \(g_d\) is not an arbitrary future quantity.  It is exactly the
service supplied at \(2d\) by the new top 2-adic divisor layer

\[
 g_d=\sum_{\substack{a\mid 2d\\a\nmid d}}b_a.
\]

Every proper divisor of \(2d\) is at most \(d\).  Thus, apart from the
current bit \(b_{2d}\), every contribution is already owned by the first
half of the orbit.  This is the missing causal asymmetry: the first half
must finance the record created at the end of the doubled block.

The recurrence at \(d\) gives

\[
 f(d)=2Q_{d-1}+t_d-Q_d\leq 2H(d)-2+t_d,          \tag{1}
\]

because \(Q_{d-1}\leq H(d)-1\) and \(Q_d\geq0\).  The recurrence at \(2d\)
gives

\[
 2R=f(2d)+Q_{2d}-t_{2d}.                         \tag{2}
\]

Consequently the single inequality

\[
 \boxed{
 g_d+Q_{2d}\leq2H(d)+t_{2d}-t_d
 }                                                \tag{EM}
\]

implies, by substituting \(f(2d)=f(d)+g_d\) into (2) and then using (1),

\[
 2R\leq4H(d)-2,
 \qquad
 R+1\leq2H(d).                                   \tag{3}
\]

Since \(2d\) is a plateau start, \(H(2d)=R+1\).  Therefore `(EM)` proves
the required `(DRMH)` inequality at this plateau.

There is an even sharper way to see what `(EM)` says.  Eliminating both
divisor loads using the recurrence gives the identity

\[
 g_d+Q_{2d}
 =2(R-Q_{d-1})+Q_d+t_{2d}-t_d.                   \tag{4}
\]

The target digits cancel from `(EM)`.  Its true content is the
phase-neutral doubled-block increment bound

\[
 \boxed{
 2(R-Q_{d-1})+Q_d\leq2H(d).
 }                                                \tag{EM'}
\]

So the sought theorem is not a pointwise estimate on the large defect
\(R\).  It says that the *new record height gained across the doubled block*,
plus the midpoint residue, cannot exceed twice the old height.  This is a
much smaller and more causal object.

## 3. Why one inequality per record is enough

On a plateau \([s,s')\) of the nondecreasing function \(H\), the margin
\(2H(d)-H(2d)\) is smallest among the \(d\) for which \(2d\) lies on that
plateau at \(d=\lceil s/2\rceil\).  Hence the full family `(DRMH)` is
equivalent to its inequalities at plateau starts.

For the actual \(1/21\) orbit, the seed is finite and every later observed
plateau start is a multiple of 20.  Thus it is even, and its midpoint is a
multiple of 10.  Since the binary word of \(1/21\) is

\[
 0.\overline{000011}_2,
\]

one has \(t_{2d}=t_d\) on these rows.  There `(EM)` becomes the particularly
transparent service budget

\[
 \boxed{f(2d)-f(d)+Q_{2d}\leq2H(d).}             \tag{EM21}
\]

The phase equality simplifies the statement, but equation (4) shows that
the essential estimate is `(EM')`.  Phase lock selects exactly the rows on
which the clean service form is available; it is not a substitute for the
inequality.

The experiment later shows that the full modulus 20 is more than this route
needs.  If \(d\) is even, then \(d\bmod6\in\{0,2,4\}\), and direct inspection
of the word `000011` gives

\[
 t_{2d}=t_d.
\]

Therefore it is enough to prove that every later record successor is
divisible by 4.  Call this weaker source-specific statement `(FAPL4)`.  The
observed `(FAPL20)` implies it, but a proof should target only the weaker
fact actually consumed by `(EMS)`.

## 4. The discriminating experiments

The companion script
`scripts/euler_midpoint_service_lab.py` performs two exact experiments.

First it decodes the packed canonical \(1/21\) itinerary, verifies its
SHA-256 digest, reconstructs \(f,Q,H\) by integer arithmetic, and audits every
even strict-record successor.  Through rank 2,000,002 all such rows satisfy
`(EM21)`.  Representative rows are

| \(2d\) | \(H(d)\) | \(g_d\) | \(Q_{2d}\) | \(2H(d)-g_d-Q_{2d}\) |
|---:|---:|---:|---:|---:|
| 20 | 2 | 1 | 1 | 2 |
| 140 | 3 | 3 | 2 | 1 |
| 420 | 5 | 6 | 1 | 3 |
| 1,441,440 | 63 | 26 | 2 | 98 |

The row at 420 is crucial.  It falsifies the tempting split

\[
 g_d\leq H(d),\qquad Q_{2d}\leq H(d),
\]

because \(g_{210}=6>5=H(210)\).  The two terms must be controlled as a
coupled service balance.  This is precisely why computation was needed: it
removes a plausible but false proof strategy before it can harden into
doctrine.

On the actual orbit an even stronger source-specific pattern is visible:

\[
 g_d+Q_{2d}\leq H(d)+2.
\]

Its maximum excess two occurs only at successors 140, 420, and 780 in the
audited range.  This strengthening is false in the rational control cohort,
so it is retained as a clue about denominator 21, not promoted to the proof
target.  `(EMS)` asks only for the weaker budget that survived adversarial
transfer.

Second, the script performs a directed-dyadic greedy census over every
reduced rational \(0<a/q<1\) with \(q\leq101\), certified through rank 1000.
It examines 3,143 targets; 1,557 remain alive through the cap.  Among their
12,112 even strict-record rows, 4,984 have both

\[
 t_{2d}=t_d,qquad H(d)\geq4.
\]

There are zero violations on this first discriminating cohort, four
equalities, and minimum margin zero.  That was enough to justify a larger
attempt to falsify it, not enough to call it a theorem.

The next stress wave uses every reduced target with denominator at most 401
and certifies the orbit through rank 2000.  It examines 49,077 targets;
24,509 remain alive through the cap.  The phase-matched, height-at-least-four
formulation now **fails three times**:

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/euler_midpoint_service_lab.py \
  --canonical-ranks 2000 --census-ranks 2000 --max-denominator 401
```

| target | \(2d\) | \(d\) | \(H(d)\) | \(g_d\) | \(Q_{2d}\) | margin |
|---|---:|---:|---:|---:|---:|---:|
| \(89/248\) | 1890 | 945 | 8 | 14 | 3 | -1 |
| \(123/341\) | 390 | 195 | 5 | 8 | 3 | -1 |
| \(12/355\) | 510 | 255 | 4 | 6 | 3 | -1 |

All three counterexamples have **odd midpoint** \(d\).  This suggested the
next structural cut.  Restrict to the geometry actually forced by the
denominator-21 phase lock: \(2d\) is a multiple of 20, so in particular
\(d\) is even.  On the larger census there are 92,418 rows satisfying

\[
 4\mid2d,\qquad t_{2d}=t_d,\qquad H(d)\geq4.
\]

Across 23,951 target prefixes there are zero violations, zero equalities,
and minimum margin one.  The still narrower multiple-of-20 cohort contains
66,558 rows across 22,006 targets, again with zero violations, zero
equalities, and minimum margin one.  Thus the experiment does not merely
confirm the first attractive conjecture: it kills it and identifies the
missing hypothesis as one more level of 2-adic divisibility at the midpoint.

These are finite exact falsification results, not a theorem.  They isolate
the sharper lemma to attack:

> **Even-midpoint service lemma `(EMS)`.**  At a strict-record successor
> \(2d\) of the actual greedy dynamics, if \(d\) is even,
> \(t_{2d}=t_d\), and \(H(d)\geq4\), then
> \(g_d+Q_{2d}\leq2H(d)\).

The census suggests the strict strengthening \(g_d+Q_{2d}\leq2H(d)-1\),
but the weak form is all the proof needs.  The threshold four is not claimed
optimal.  Small-height exceptions are finite seed phenomena in the intended
application.

### Nested-height refinement

The follow-on exact experiment
[`NewtonNestedHeightFrontier.md`](NewtonNestedHeightFrontier.md) finds a
strictly sharper coupled target:

\[
 \boxed{
 g_d+Q_{2d}\le H(d)+H(d/2)+t_{2d}-t_d.
 }                                                \tag{NH}
\]

For even \(d\), monotonicity gives \(H(d/2)\le H(d)\), so `(NH)` implies
`(EM)` immediately.  In the phase-neutral coordinate it is

\[
 2(R-Q_{d-1})+Q_d\le H(d)+H(d/2).                \tag{NH'}
\]

This is not the sum of two independently valid estimates.  In the exact
denominator-at-most-401 census, the two tempting pieces

\[
 R-Q_{d-1}\le H(d/2),
 \qquad
 R-Q_{d-1}+Q_d\le H(d)
\]

fail twice each, while their coupled sum has zero violations on all 92,418
selected rows and 72 equalities.  Exact rational tail-gap splices then make
`(NH)` fail after the terminal all-take regime begins.  Thus `(NH)` is now the
most compressed service producer, but its proof must consume the true greedy
boundary; it is not a carry-only law.

### Fatal escape makes the record set cofinite

The follow-on analysis
[`RecordCofinitenessBoundary.md`](RecordCofinitenessBoundary.md) shows that
`(FAPL4)` is stronger than the endpoint needs.  A final skip leaves a positive
residual amplitude, and the exact defect decomposition gives

\[
 Q_N/2^N\longrightarrow\delta>0.
\]

Since `f(N)<=N`, the recurrence eventually forces `Q_N>Q_(N-1)`; after the
finite earlier maximum is passed, every rank is a strict record.  Thus any
cofinal supply of non-record ranks rules out the fatal branch.  Exact rational
gap splices exhibit this transition and violate `(FAPL4)` in all four residue
classes.

One may therefore bypass both midpoint producers by proving arbitrarily late
one-step repairs

\[
 f(N)\ge Q_{N-1}+t_N,
\]

which make `N` a non-record and directly exclude final escape.

## 5. The exact route to a proof

The computation leaves a two-lemma midpoint route, followed only by already
proved implications.

1. **Nested-height service.**  Prove `(NH)`, which implies `(EMS)`, preferably
   through the phase-neutral form `(NH')`.  The decisive new input is \(2\mid d\): the
   fresh service \(g_d\) is the next layer in the 2-adic divisor tower,
   immediately above the layer already visible between \(d/2\) and \(d\).
   The proof must exploit the compensation between quarter-block gain and
   midpoint residue together with the actual greedy boundary.  Bounding the
   two terms separately is false by the exact controls above.
2. **Quarter-phase record lock.**  Prove `(FAPL4)`: every non-seed strict
   record of the actual \(1/21\) orbit has successor divisible by 4.  Writing
   that successor as \(2d\), this makes \(d\) even, and the period-six word
   automatically gives \(t_{2d}=t_d\).  The stronger observed `(FAPL20)` is
   sufficient but unnecessary.  Handle the finitely many rows with
   \(H(d)<4\) directly: the exact prefix through 159 contains only the seed
   and plateau starts 20, 80, and 140, while \(H(80)=4\); hence every start
   \(2d\geq160\) has \(H(d)\geq4\).
3. `(EM)` then proves `(DRMH)` at every plateau start by (1)--(3); the
   plateau reduction proves `(DRMH)` for every \(d\).
4. Iterating `(DRMH)` from \(H(20)=3\) gives a global linear defect bound.
5. The existing Lean theorem turns any subexponential defect bound into
   \(1/21\) membership in the Mersenne achievement set.
6. The existing target-specific theorem `finiteErdosSum_ne_one_div_twenty_one`
   proves that no finite Mersenne support represents \(1/21\).  Hence the
   representing support is infinite, giving the negative answer to Erdős
   problem 257.

Alternatively, prove a cofinal non-record or one-step-repair supply and invoke
the record-cofiniteness boundary theorem directly; this avoids Steps 1--4.
No finite computation can replace either all-depth/cofinal producer.  But the
search has now changed character: instead of trying
to control an unbounded carry history, it asks why a first-half greedy
orbit, at an even midpoint, must provide enough service in the *next 2-adic
divisor layer* to pay for the record increment across one doubled block.

## 6. Why the affine escape route is not currently competitive

The exact actual-prefix boundary identity and affine cocycle remain useful
diagnostics, but positivity does not see the homogeneous coefficient, and
adaptive skipped-divisor corrections can carry the endpoint's irrational
weighted class.  Without an independent subexponential estimate that route
returns to the same missing growth control.

`(EM')` is different.  It cancels the future reset term exactly, survived
after its first overgeneralization was destroyed by a deeper adversarial
census, and plugs directly into the shortest checked endpoint.  The
even-midpoint version `(EMS)` is now the highest-information proof target.

## 7. Proof boundary

This note proves only the algebraic implication

\[
 \text{(EM at the relevant record starts)}
 \Longrightarrow \text{(DRMH)}
 \Longrightarrow \text{the existing membership endpoint}.
\]

It does **not** prove `(EMS)`, the all-depth record phase lock, \(1/21\)
membership, or Erdős problem 257.  The computation has found a precise route
and destroyed weaker routes; the two all-depth lemmas still require proof.
