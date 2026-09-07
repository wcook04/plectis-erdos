# The fatal branch makes every late rank a record

> **Status update (2026-08-23, deep audit).**  The periodic repair producers
> named in §5 below — `(M120R)`, `(PM120)`, and their unconditional form
> `(CD120)` — are **falsified** on the validated zero-undecided orbit: first
> `(M120R)` violation at rank 5,686,680, six violations and minimum margin −3
> by rank 20,000,002, all on prime-cofactor columns (`(PM120)` already fails at
> 3,175,080).  See
> [`TwentyOneRepairSupplyDeepAudit.md`](TwentyOneRepairSupplyDeepAudit.md)
> for exact certificates.  The global repair census itself survives the whole
> horizon (density 0.443, maximum gap 11), so the live producer is the weaker
> **cofinal-repair guarantee `(CRG)`** of that note; its Lean consumer chain
> (`TwentyOneCofinalRepairConsumer.lean`) lands as a separate validated wave
> behind the project build lease.  §5's `(PU120)`-family falsification
> and this result leave §4's route structure unchanged: only the periodic
> subfamily is dead, not the cofinal supply.

Status: exact analytic reduction with exact rational boundary controls,
2026-08-23.  This does not claim a solution of Erdős problem 257.

## 1. The record-phase conjecture is stronger than necessary

For the canonical greedy support of `1/21`, write

\[
 f(n)=\sum_{a\mid n}b_a,
 \qquad Q_n=2Q_{n-1}+t_n-f(n).
\]

The nested-height route proposed `(FAPL4)`: after the finite seed, every
strict record rank `n` should satisfy `4 | n+1`.  That is sufficient for the
even-midpoint service law, but it hides a much weaker boundary fact.

> **Record-cofiniteness boundary theorem.** If the `1/21` greedy orbit has a
> final skip, then every sufficiently late rank is a strict record of `Q`.

Consequently it is enough to prove that non-record ranks occur beyond every
cutoff.  One does not need to classify every record modulo four or twenty.

## 2. Proof of the boundary theorem

Assume the last skipped rank is `L`.  All ranks greater than `L` are selected.
The greedy remainder therefore decreases to the positive fatal-gap amplitude

\[
 \delta=r_L-\sum_{n>L}\frac1{2^n-1}>0.
\]

The exact defect decomposition already proved in Lean is

\[
 Q_N+\frac{2^N\bmod21}{21}
 =2^N r_N+F_N,                                    \tag{1}
\]

where the finite-prefix divisor tail satisfies `0 <= F_N = O(sqrt N)`.
Since `r_N -> delta`, division by `2^N` in (1) gives

\[
 \frac{Q_N}{2^N}\longrightarrow\delta>0.          \tag{2}
\]

In particular `Q_(N-1)>N` for all sufficiently large `N`.  Booleanity alone
gives `f(N)<=tau(N)<=N`, while `t_N>=0`.  Hence

\[
 Q_N-Q_{N-1}=Q_{N-1}+t_N-f(N)>0                  \tag{3}
\]

eventually.  The sequence is then strictly increasing and unbounded.  After
it passes the finite maximum attained before (3) becomes permanent, every
subsequent rank is a new strict record.  This proves the theorem.

The argument uses the positive boundary amplitude.  It is not a recurrence-
only phase lemma and cannot be valid on a surviving orbit for the same reason.

## 3. Exact discriminating controls

The companion executable
`scripts/record_cofiniteness_boundary_lab.py` compares the canonical orbit
with exact rational gap splices.  Each splice preserves the canonical prefix,
skips at a prescribed rank, and then takes every later coin.  No floating
point is used.

For fatal ranks `40`, `80`, `140`, and `200`, every splice develops a terminal
suffix in which every single rank is a strict record.  Its strict records use
all four successor residue classes modulo four, so `(FAPL4)` fails.  This is
the opposite of the packed canonical `1/21` orbit, whose mature records all
have successors divisible by four and whose record set remains extremely
sparse through the audited horizon.

The controls show that `(FAPL4)` and `(NH)` are not independent local laws.
Both distinguish the same global boundary: `(FAPL4)` fails first as the
homogeneous component begins to dominate, and `(NH)` fails later when the
record increments become exponential.

## 4. The reduced proof route

The shortest record-based route is now:

1. prove a cofinal supply of ranks `N` which are not strict records of `Q`;
2. the boundary theorem rules out a final skip;
3. the Lean-checked cofinal-skip characterization gives
   `1/21` membership in the Mersenne achievement set;
4. `finiteErdosSum_ne_one_div_twenty_one` forces the representing support to
   be infinite, disproving Erdős 257.

A convenient sufficient producer at a rank `N` is the one-step repair

\[
 f(N)\ge Q_{N-1}+t_N,
\]

because then `Q_N<=Q_(N-1)` and `N` is not a strict record.  Only a cofinal
subsequence of such repairs is needed.  This is strictly weaker than `(RB4)`,
`(RR)` at every record successor, `(FAPL4)`, `(NH)`, or a global defect bound.

What remains open is precisely that cofinal repair/non-record producer.  The
finite canonical orbit suggests many candidates, but a horizon cannot supply
the quantifier.

## 5. The arithmetic-progression repair candidate

The next exact probe uses the full packed orbit through rank `2,000,002`.
One-step repairs occur with maximum observed gap `10`.  More importantly,
every tested multiple of `120` is a repair:

\[
 \boxed{f(120k)\ge Q_{120k-1}+t_{120k}.}          \tag{M120R}
\]

This is the sharpest present producer.  An all-depth proof of `(M120R)` gives
cofinally many non-records immediately and therefore disproves Erdős 257 by
the route above.  The modulus is structurally suggestive rather than fitted:
`lcm(6,20)=60` and `120=2*lcm(6,20)`.  Multiples of `60` have exact failures,
whereas all `16,666` multiples of `120` through two million pass.  Thus the
extra 2-adic layer is substantive finite evidence, not a proved explanation.

The computation actually supports a stronger, entirely causal statement.
Write

\[
 g(n)=\sum_{\substack{d\mid n\\d<n}}b_d.
\]

All `16,666` tested rows satisfy

\[
 \boxed{g(120k)\ge Q_{120k-1}+1.}                \tag{PM120}
\]

There are three equalities, at `999480`, `1699080`, and `1905240`.  The current
bit `b_(120k)` is therefore unnecessary: selected proper divisors alone pay
the repair bill.

More sharply still, let `U_30(n)` count only selected `d` which divide at
least one of `n/2,n/3,n/5`.  Inclusion-exclusion gives the seven-column form

\[
\begin{aligned}
 U_{30}(n)={}&f(n/2)+f(n/3)+f(n/5)\\
             &-f(n/6)-f(n/10)-f(n/15)+f(n/30).
\end{aligned}
\]

Every tested multiple of `120` satisfies

\[
 \boxed{U_{30}(120k)\ge Q_{120k-1}+1,}           \tag{PU120}
\]

with exactly the same three equality rows.  Each counted bit lies at rank at
most `n/2`, so `(PU120)` is a finite, past-owned seven-column inequality; it
implies `(PM120)`, `(M120R)`, and `(CD120)`.  The three two-prime subunions do
not suffice: the `{2,3}`, `{2,5}`, and `{3,5}` versions have respectively 11,
1, and 77 exact violations through two million.  Thus all three primes in
`30` are structurally active in the observed law.

The period-six target pulse also cancels exactly.  Let `J^-(n)` and `J(n)`
denote the same seven-term inclusion-exclusion operator applied respectively
to `Q_(n/q-1)` and `Q_(n/q)` for
`q in {2,3,5,6,10,15,30}`.  At `n=120k`, the corresponding target-digit
combination is `1=t_n`.  Substituting
`f(m)=2Q_(m-1)+t_m-Q_m` into `(PU120)` gives the phase-free form

\[
 \boxed{2J^-(n)-J(n)\ge Q_{n-1}.}               \tag{PF120}
\]

The independently generated `4/9` cylinder selects the same modulus, the
same seven columns, and the same phase-free inequality: its target pulse and
`t_(120k)` are both zero.  Through ten million ranks, `4/9` has `83,333`
`(PF120)` rows, zero violations, zero equalities, and minimum margin one; the
tightest rows are `3175080` and `8754360`.
Thus `(PF120)` is now a cross-target theorem candidate rather than an isolated
denominator-21 congruence.  It remains source-conditioned: unrelated rational
survivors can violate the phase-free form when their target pulse does not
equal their current digit.

## 6. The unconditional form, and a conditional future-column normal form

The target-defect recurrence itself gives, with no representation hypothesis,

\[
 Q_n=2Q_{n-1}+t_n-f(n).
\]

Thus at `n=120k`, where `t_n=1`, `(M120R)` is exactly

\[
 \boxed{Q_n\le Q_{n-1}.}                         \tag{CD120}
\]

This is the noncircular all-depth target: the denominator-21 defect carry must
never rise across a multiple-of-120 column.

There is also a useful but **conditional** representation-side normal form.
For any Boolean support `A` which is already known to represent a real target
`x`, the Lambert identity gives

\[
 Q_{n-1}
 =\left\lfloor
   \frac{f(n)}2+\frac{f(n+1)}4+\frac{f(n+2)}8+\cdots
  \right\rfloor.                                 \tag{FQ}
\]

If in addition `x=1/21`, then at `n=120k` the denominator-21 digit is `t_n=1`
and `{2^(n-1)/21}=11/21`.  Consequently `(M120R)` is equivalent to the
divisor-column inequality

\[
 \boxed{
   \sum_{r\ge1}\frac{f(n+r)}{2^r}<f(n).
 }                                                \tag{FCD120}
\]

Indeed the expression inside the floor in `(FQ)` has fractional part
`11/21`.  If

\[
 m=f(n)-Q_{n-1}-1,
\]

then the exact dominance margin is quantized:

\[
 f(n)-\sum_{r\ge1}\frac{f(n+r)}{2^r}
 =2m+\frac{20}{21}.                              \tag{QM}
\]

Under the representation hypothesis, the tight audited row `n=999480` with
`m=0` would therefore have infinite-column margin exactly `20/21`.

This normal form may diagnose what a successful representation looks like,
but it cannot prove `(M120R)`: identifying `Q` with the future divisor tail
already assumes that the greedy support sums to `1/21`, which is the desired
conclusion.  Using `(FCD120)` to prove membership would be circular.  The proof
search must remain on the unconditional carry-descent statement `(CD120)` or
derive the needed identification from an independently stronger hypothesis.

## 7. Two tempting explanations are false

The rational survivor census supports the stronger repair inequality using
`U_30`, not merely `(M120R)`: all `12,456` tested multiple-of-120 rows from
`1,557` unrelated certified survivors pass.  The phase-free form `(PF120)`
does have control failures, exactly when the control target's seven-term digit
pulse differs from `t_n`; the actual repair margin remains nonnegative.
Survivor conditioning is essential.

Nor do the six permanently selected anchor divisors

\[
 \{5,8,10,20,24,60\}\subseteq A
\]

prove the law.  There is an exact finite-support countermodel.  Set
`n=1962960`; then

\[
 n+1=7\cdot11\cdot13\cdot37\cdot53
\]

has 32 divisors.  Take the six anchors together with all 31 nontrivial
divisors of `n+1`.  The resulting Mersenne subsum is below

\[
 \frac6{31}+\frac{31}{127}<1.
\]

At column `n` only the six anchors contribute, so `f(n)=6`.  Immediately
before it, every anchor contributes more than `1/2` to `(FQ)` and every
selected divisor of `n+1` contributes more than `1/4`.  Hence the coordinate
inside the floor exceeds

\[
 6/2+31/4=43/4,
\]

so `Q_(n-1)>=10` and `(M120R)` fails by at least four units.  Thus a proof for
`1/21` must control the actual selected divisor columns after `120k`; fixed
anchors, Booleanity, achievement-set membership, and the modulus alone do not
do so.

The next proof experiment should attack `(CD120)` directly using the exact
`1/21` source boundary and the extra 2-adic layer.  A finite count is not the
proof, and `(FCD120)` is only a conditional diagnostic.

Reproduction:

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/\
  record_cofiniteness_boundary_lab.py --canonical-ranks 200000
```
