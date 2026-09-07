# Divisor ancestry widens record repair beyond dyadic children

Status: exact finite opening on the bound two-million-rank denominator-21
orbit, 2026-08-22.  The all-depth statement below is a conjecture, not a
proof of Erdős Problem 257.

## 1. From dyadic inheritance to arbitrary record ancestors

The strict-record computation in
[`TwentyOneComputationalStructureLab.md`](TwentyOneComputationalStructureLab.md)
tests the repair inequality

\[
 f(n+1)\geq Q_n+t_{n+1}                         \tag{RR}
\]

whenever `n` is a strict record of the denominator-21 Lambert defect `Q`.
The companion
[`TwentyOneRecordDivisorSupplyNoGo.md`](TwentyOneRecordDivisorSupplyNoGo.md)
eliminates static half-density explanations but finds a positive inheritance
mechanism: if strict records satisfy `n=2r+1`, then `r+1` divides `n+1`, so
the selected-divisor load at the older successor is inherited by the new
successor.

The divisibility argument is not specifically dyadic.  For a strict record
`n`, define

\[
 A(n)=\max\{f(r+1): r<n\text{ is a strict record and }r+1\mid n+1\},
\]

with `A(n)=0` if there is no eligible ancestor.  Every selected divisor
counted by `A(n)` is also counted by `f(n+1)`.

## 2. The finite candidate `(AI8)`

All 39 strict records in the exact replay through rank `2,000,002` satisfy

\[
 \boxed{A(n)+8\geq Q_n+t_{n+1}.}                 \tag{AI8}
\]

The additive constant eight is sharp on this finite record set.  Constant
seven fails at `n=13859`: the best earlier record successor is `420`, whose
selected-divisor load is `12`, while the repair bill is `20`.

This is not merely the dyadic chain in different notation.  It also reaches
records with no direct dyadic record parent.  For example, the root record
`n=1081079` inherits from record successor `360360`:

\[
 360360\mid1081080,
 \qquad f(360360)=102,
 \qquad Q_{1081079}+t_{1081080}=67.
\]

The inherited margin there is `35`.  The tightest late root example is
`n=1053359`, where successor `95760` supplies `64` against a repair bill of
`65`, leaving only one unit for the additive allowance.

The raw inherited margin is nonnegative at 24 of the 39 records.  The fifteen
negative-margin ranks are persisted in the receipt, as is the best ancestor
and exact divisor quotient for every record.  This separates the successful
inheritance edges from the finite additive slack rather than hiding both in a
single pass count.

## 3. The best ancestor collapses to a canonical parent

The maximum in `A(n)` could have been an unhelpful best-of-many choice.  On
the exact record set it is not: whenever eligible ancestors exist, the
numerically largest earlier record successor dividing `n+1` also has the
largest selected-divisor load.  Call its record rank `p(n)`, and give an
absent parent load zero.  The same data therefore verify the canonical form

\[
 \boxed{f(p(n)+1)+8\geq Q_n+t_{n+1}.}             \tag{P8}
\]

There is a parent at 37 of the 39 records; only the seed ranks `6` and `19`
lack one.  The largest observed quotient `(n+1)/(p(n)+1)` is `39`.  Thus the
finite result does not require searching across ancestry: one divisor-selected
parent is determined by the record ranks alone.

This collapse is not automatic from a hidden divisibility chain.  That
explanation already fails at record `139`: both record successors `7` and
`20` divide `140`, while neither divides the other.  Eligible ancestry is
branching at 32 of the 39 checked records.  Nevertheless the largest eligible
successor maximizes the selected load every time.  The receipt names this
separate finite candidate `(LPD)` and persists every eligible ancestor so that
future probes can falsify it without replaying the greedy orbit.

## 4. A weaker polynomial genealogy producer

The divisor loads can be discarded altogether.  Along the same canonical
parent edges, all 37 tested non-seed records satisfy

\[
 Q_n\leq 4Q_{p(n)}.                               \tag{GP4}
\]

In fact the sharper finite inequality `2Q_n<=7Q_{p(n)}` holds, with equality
at record `779`, whose parent is record `19`.  The maximum checked genealogy
depth is eight, reached at record `655199`.

This weaker statement is already a complete producer.  A proper
record-successor divisor is at most half the child successor, so a parent
chain ending at `n` has length at most `log_2(n+1)`.  Iterating `(GP4)` gives

\[
 Q_n=O\!\left(4^{\log_2(n+1)}\right)=O((n+1)^2)
\]

at strict records.  Every intermediate defect is bounded by the latest strict
record, so the same polynomial envelope holds everywhere.  Polynomial defect
is subexponential and therefore feeds the already checked membership theorem.

This changes the proof target materially: it is unnecessary to prove `(RR)`,
`(P8)`, or any lower bound on a selected-divisor load.  It would suffice to
prove two record-genealogy facts after the finite seeds: a divisor parent
always exists, and defect grows by at most factor four along the canonical
parent edge.  The exact falsifiers are a parentless later record or an edge
with `Q_n>4Q_{p(n)}`.

### Cross-target falsification control

The exact control panel in
[`rational_record_genealogy_control.py`](../../scripts/rational_record_genealogy_control.py)
shows that `(GP4)` is not a generic consequence of a random-looking support
word.  The sharpest comparison uses

\[
 \frac4{21}=\frac1{21}+\frac1{2^3-1}.
\]

Through rank `10080`, the two greedy supports differ only at rank `3`.
Nevertheless `(GP4)` has no violation for `1/21` and fails for `4/21` at
records `419` and `779`; at the latter record the child/parent defect ratio is
eight.  Thus even a finite support shift can change the strict-record carry
genealogy while leaving the entire tail support identical.

This is useful negative information.  A proof of `(GP4)` for `1/21` cannot be
a support-generic, divisor-poset, or pseudorandom-word lemma.  It must retain
the exact period-six source bits of `1/21`.  The canonical receipt
`state/formal_math/erdos257_period_noncollapse/rational_record_genealogy_control_receipt.json`
binds ten targets, the exact falsifier rows, the independent `1/21` itinerary
check, and this analysis surface.

### Shift-robust repair: weak-record parents

The failure mechanism above is exact: adding one coin changes the carry defect
by a zero-or-one floor carry, which can turn an old strict record into a tied
running maximum and remove it from the strict-parent pool.  Retaining those
ties repairs the genealogy.  Call `r` a weak record when

\[
 Q_r=\max_{k\leq r}Q_k,
\]

and allow a strict child record to use the largest earlier weak record whose
successor divides the child successor.  The resulting candidate is

\[
 \boxed{Q_n\leq4Q_r.}                            \tag{WGP4}
\]

[`twenty_one_weak_record_genealogy.py`](../../scripts/twenty_one_weak_record_genealogy.py)
is a downstream consumer of the schema-`v1` packed itinerary: it reconstructs
the divisor convolution and all defects without replaying the quotient
recurrence.  Through the canonical `500002` ranks it finds 34 strict records,
103 weak records, a weak parent for every strict record after the seed at rank
`6`, and zero factor-four violations.  The sharp finite ratio remains `7/2`
at record `779`, now using weak parent `77`, whose defect plateau was created
by strict record `19`.

`(WGP4)` keeps the polynomial consequence.  If weak parent `r` lies on the
plateau created by strict record `s`, then `Q_r=Q_s` and

\[
 s+1\leq r+1\leq\frac{n+1}{2}.
\]

Recursive descent through `s` therefore has logarithmic depth and multiplies
the defect by at most four per generation, giving `Q_n=O(n^2)`.  Unlike strict
`(GP4)`, weak `(WGP4)` also has zero violations on all ten exact control
targets through rank `10080`; this does not prove universality, but it removes
the finite-support-shift fragility without sacrificing the one-way result.

The canonical receipt
`state/formal_math/erdos257_period_noncollapse/twenty_one_weak_record_genealogy_receipt.json`
binds the decoded itinerary, source and control payload digests, every weak
parent edge, the plateau source, and the downstream membership consequence.

### Normalized defect monotonicity

The factor four can be removed.  If `q=(n+1)/(r+1)` is the exact successor
quotient on a weak-parent edge, every checked `1/21` edge satisfies

\[
 Q_n\leq qQ_r,
 \qquad\text{equivalently}\qquad
 \frac{Q_n}{n+1}\leq\frac{Q_r}{r+1}.             \tag{WGN}
\]

This is sharper than `(WGP4)` on the 25 quotient-two edges and adapts
automatically on the eight fallback edges with quotients `3`, `10`, `11`, or
`13`.  It has zero violations through rank `500002`; equality occurs, so the
finite test is not vacuous slack.

The normalized form has the cleanest downstream descent.  If `r` lies on the
plateau created by strict record `s`, then `Q_r=Q_s` and `s<=r`, hence

\[
 \frac{Q_n}{n+1}
 \leq\frac{Q_r}{r+1}
 \leq\frac{Q_s}{s+1}.
\]

Iteration reaches the seed `(s,Q_s)=(6,1)` and gives

\[
 Q_n\leq\frac{n+1}{7}
\]

at every strict record, therefore at every rank.  This linear bound is already
subexponential and closes the checked `1/21` membership route.

The cross-target control makes the scope precise.  Nine of ten targets have
zero normalized weak-parent failures through rank `10080`; `1/5` fails once at
the finite-seed record `29` and never later in the checked range.  Thus `(WGN)`
is not being presented as a universal theorem, but its only control failure is
an explicit early seed exception rather than the finite-shift collapse that
killed strict `(GP4)`.

The canonical orbit supports a stronger parent-choice-free form.  Across all
1,019 pairs `(n,r)` where `n` is a strict record, `r<n` is a weak record, and
`r+1` divides `n+1`, the normalized inequality holds:

\[
 \boxed{\frac{Q_n}{n+1}\leq\frac{Q_r}{r+1}}
 \qquad\text{for every eligible edge}.           \tag{EWGN}
\]

There are no finite violations, and the equality edges are stored rather than
rounded away.  This decomposes the theorem target without a best-parent rule:

1. every strict record after rank `6` has at least one weak divisor parent;
2. normalized defect density cannot increase on any eligible edge.

If both clauses hold at all depths, any eligible parent gives the same linear
descent.  The receipt now persists the complete 1,019-edge table, so future
computations can test either clause independently and proof work need not
reverse-engineer which parent the earlier script selected.

The divisor hypothesis is not decorative.  If it is removed and normalized
density is compared merely along successive strict records, monotonicity fails
four times through rank `500002`.  The first failure is

\[
 \frac{Q_{839}}{840}=\frac8{840}
 \,>\,
 \frac{Q_{779}}{780}=\frac7{780}.
\]

Later failures occur at records `32759`, `332639`, and `360359`.  Thus `(EWGN)`
does not follow from a generic slow growth of record heights: all 1,019
divisor-compatible edges pass while explicit adjacent non-divisor comparisons
fail.  The receipt stores every adjacent comparison and the four falsifiers.

### Two-million packed-source discriminator

The independent schema-`v1` replay through rank `2000002` has packed itinerary
digest
`f4acc653489d3d5af1c69b8d065e692ef9f83c566a569bc73704667b6d051413`,
exactly matching the immutable historical replay.  Projecting its enriched
strict-record rows onto the old row schema gives an exact row-for-row match.
Its payload digest is
`0a280a12350af6c9a88d09de7683268111b0e16b3b71808602b4a1bfa42ea3db`.

Running the parameterized packed-itinerary consumer on this source adds ten
weak records and 291 eligible edges.  The resulting totals are 39 strict
records, 113 weak records, and 1,310 complete eligible edges, with no
parentless record after the seed and zero `(WGP4)`, `(WGN)`, or `(EWGN)`
violations.  The five new strict records have these chosen weak parents:

| child `n` | `Q_n` | weak parent `r` | `Q_r` | quotient | normalized margin |
|---:|---:|---:|---:|---:|---:|
| 655199 | 56 | 327599 | 46 | 2 | 36 |
| 720719 | 62 | 360359 | 51 | 2 | 40 |
| 1053359 | 64 | 526679 | 52 | 2 | 40 |
| 1081079 | 66 | 360359 | 51 | 3 | 87 |
| 1441439 | 75 | 720719 | 62 | 2 | 49 |

The rank `1053359` row is the discriminating case.  It was a root for the
strict-record genealogy, but its weak parent `526679` lies on the plateau
created by strict record `480479`.  Thus tied-record retention repairs a new
deep root, not just the finite-support-shift control at rank `779`.  The other
old strict root, `1081079`, receives a quotient-three weak edge from strict
record `360359`.

The non-divisor control becomes more adverse at the same checkpoint:
successive strict-record density now fails six times, adding failures at
`720719` and `1081079`.  Hence the survival of all 291 new divisor-compatible
edges cannot be attributed to a late global density trend.  The downstream
receipt is
`state/formal_math/erdos257_period_noncollapse/twenty_one_weak_record_genealogy_receipt_2000002.json`,
with canonical payload digest
`cb79707fcb6a19c144fa2cf1e9e0939b1f1b372fc6f5d4975ba33ba386bb33fc`.

### The native carry shift separates contraction from parent supply

The checked membership theorems normalize `Q+1`, not `Q`.  This suggests the
slightly weaker edge inequality

\[
 \boxed{\frac{Q_n+1}{n+1}\leq\frac{Q_r+1}{r+1}}
 \qquad\text{whenever }r+1\mid n+1.              \tag{SEWGN}
\]

The `+1` is arithmetically active rather than cosmetic.  The exact census in
[`rational_weak_record_genealogy_census.py`](../../scripts/rational_weak_record_genealogy_census.py)
enumerates every reduced target `a/q` in `(0,1)` with `q<=101`, certifies its
greedy orbit by directed integer intervals and rigorous tail bounds, and keeps
the 1,557 targets alive through rank `1000`.  On the largest eligible weak
parent, the unshifted `(WGN)` inequality fails 139 times across 138 targets.
Across all eligible edges it fails 157 times.  By contrast, `(SEWGN)` has zero
failures on all 94,286 eligible edges.  Its 138 equality edges rule out an
explanation by generous numerical slack.

This census changes the theorem selection.  Shifted density contraction now
looks like a broad survivor-genealogy law, whereas parent supply does not:
131 alive targets have a later strict record with no weak divisor parent, for
139 parentless events in total.  The `1/21` prefix has neither kind of failure.
Thus the two clauses should not be attacked as one source-specific miracle:

1. seek a general greedy-survivor proof of `(SEWGN)` on every existing edge;
2. use the exact period-six `1/21` source to prove that an edge always exists.

The census supports a still cleaner formulation of the first clause.  Define

\[
 H(m)=1+\max_{0\leq k<m}Q_k.
\]

At a weak record `r`, `H(r+1)=Q_r+1`; at a strict record `n`,
`H(n+1)=Q_n+1`.  Consequently `(SEWGN)` is an instance of the
multiplicative running-maximum envelope

\[
 H(qd)\leq qH(d).                                  \tag{PMRMH}
\]

The unrestricted version is false in the rational census: among 9,460,332
tested multiplicative horizon pairs there are 172 violations across 51
targets.  Every one has the same exact finite-seed shape

\[
 H(d)=1,\qquad q=2,\qquad H(2d)=3,
\]

and hence margin `-1`.  Once the positive-base hypothesis `H(d)>=2` is
imposed, there are zero violations on 6,222,398 tested pairs and 925 equality
pairs.  A weak-record parent automatically supplies this hypothesis.  Thus a
proof of `(PMRMH)` would prove the entire edge clause without mentioning
records or divisor convolutions.

This absence of small-denominator violations is not a universal tail theorem.
The exact support

\[
 A_*=\{2,3,4,7,9,11,15,16,22,44,45,46,47,48\}
\]

has rational value

\[
 x_*=
 \frac{54978650545243844890212602434232295057285189597770659004880898041598}
 {99378887306383794336179566198166351541803714282061319632787512746805}.
\]

Exact greedy replay of `x_*` selects precisely `A_*` and terminates with zero
remainder at rank `48`.  For any exactly represented support, the defect is
the floor of its divisor tail,

\[
 Q_k=\left\lfloor\sum_{d\in A}
       \frac{2^{k\bmod d}}{2^d-1}\right\rfloor .
\]

Evaluating this identity for `A_*` gives

\[
 H(22)=2,\qquad H(44)=5>4=2H(22).
\]

The violation is not caused by termination.  Adjoin every rank `d>=100`.
For `k<44` the added tail is strictly below
`2^(k+2-100)`; this is smaller than every relevant integer-floor slack, so
the infinite extension still has `H(22)=2` and `H(44)=5`.  Hence `(PMRMH)` is
neither support-universal nor implied by exact greedy representability.  A
proof for `1/21` would have to exploit arithmetic of that actual orbit, so the
candidate remains selective rather than collapsing to a disguised membership
identity.  The schema-`v3` census receipt stores the exact target, support,
greedy replay, tail witnesses, and infinite-extension bounds.

More importantly, the full envelope is itself a one-way producer.  For the
actual denominator-21 greedy carry, fix `d=20`, where `H(20)=3`.  Given any
`N>=20`, put `q=ceil((N+1)/20)`.  Monotonicity of `H` and `(PMRMH)` give

\[
 Q_N+1\leq H(20q)\leq3q
 \leq\frac{3(N+20)}{20}.                          \tag{PMRMH-linear}
\]

This is a global linear defect bound.  Therefore an all-depth proof of
`(PMRMH)` for the concrete `1/21` orbit reaches membership and infinite
support directly; it needs neither parent existence nor a record phase lock.

The packed `1/21` orbit supports the unrestricted envelope as well.  Through
rank `500002`, all 6,138,466 multiplicative horizon pairs pass, with three
equalities.  Through rank `2000002`, all 27,326,307 pairs pass with the same
three equalities.  On the positive-base restriction the respective counts are
4,913,468 and 22,426,309, with minimum integer margin one and no equality.
These complete multiplicative-pair tables are summarized in the schema-`v2`
weak-genealogy receipts, rather than existing only as a record-edge sample.

### Doubling is the minimal multiplicative producer

The all-quotient law is stronger than the consequence uses.  Its doubling
specialization is

\[
 \boxed{H(2d)\leq2H(d).}                          \tag{DRMH}
\]

Starting from `H(20)=3`, iteration gives

\[
 H(20\cdot2^j)\leq3\cdot2^j.
\]

For an arbitrary horizon, round upward to the next member of this dyadic
chain and use monotonicity of `H`.  The minimality of the power of two makes
the resulting bound linear in the original horizon.  Thus `(DRMH)` alone is a
one-way membership and infinite-support producer; no quotient other than two,
record parent, or phase lock is required.

The packed orbit tests exactly this reduced surface.  Through horizon
`500003`, all 250,001 doubling pairs pass; through horizon `2000003`, all
1,000,001 pass.  Restricting to `H(d)>=2` leaves 249,995 and 999,995 pairs,
respectively, with minimum integer margin one and no equality.  Along the
actual dyadic chain the observed heights are

\[
\begin{array}{c|rrrrrrrrrrrrrrrrr}
d&20&40&80&160&320&640&1280&2560&5120&10240&20480&40960&81920&163840&327680&655360&1310720\\
\hline
H(d)&3&3&4&5&6&7&9&12&15&19&23&27&32&39&47&57&67.
\end{array}
\]

The obvious route to `(DRMH)` through a stronger subadditivity theorem is
closed by exact actual-orbit counterexamples.  The law

\[
 H(a+b)\leq H(a)+H(b)
\]

first fails at

\[
 (a,b)=(1,3359),\qquad 1+12<14=H(3360).
\]

Even the positive-base restriction `H(a)>=2` and `H(b)>=2` first fails at

\[
 (a,b)=(7,110873),\qquad 2+34<37=H(110880).
\]

Through two million ranks there are 36 violating plateau pairs in the
unrestricted control and 17 in the positive-base control; the strongest
margins are `-8` and `-7`.  Therefore `(DRMH)` must use the exact symmetric
doubling geometry.  Ordinary translation/subadditivity cannot be proved first
and specialized afterward.  These rows and falsifiers are builder-owned in
the schema-`v2` weak-genealogy receipts.

### The doubling family collapses to plateau-start halves

`(DRMH)` is not a million-pair statement.  On each plateau `[s,s')` of `H`,
the doubling margin `2H(d)-H(2d)` is minimized, over all `d` with `2d` in the
plateau, at the single point `d = ceil(s/2)`: there `H(2d)` is constant equal
to the plateau height while `H(d)` is nondecreasing.  Therefore

\[
 \text{(DRMH) holds for every } d
 \iff H(s)\leq 2H(\lceil s/2\rceil)\ \text{at every plateau start } s.
\]

The schema-`v2` receipts verify this reduction losslessly (the per-plateau
empirical minimum equals the representative margin at every plateau) and
test the reduced surface.  Through horizon `500003` there are 35 plateau
rows; through horizon `2000003` there are 40.  All pass, with zero
violations and zero representative mismatches.  The minimum positive margin
is exactly `1`, attained only at the seed row `s=1` and at the record rows

| `n` | `s=n+1` | `H(s)` | `d=s/2` | `H(d)` | margin |
|---|---|---|---|---|---|
| 19 | 20 | 3 | 10 | 2 | 1 |
| 139 | 140 | 5 | 70 | 3 | 1 |

Every later record row has margin at least `2` and the margins grow
steadily (the last row: `n=1441439`, `H=76`, `d=720720`, `H(d)=63`,
margin `50`).  Combined with `(FAPL20)` every later plateau start is
`0 mod 20`, so the check points are `s/2 = 0 mod 10`.  An all-depth proof
of `(DRMH)` therefore needs exactly one inequality per future record,
`Q_n+1 <= 2H((n+1)/2)`, and the tight rows at `19` and `139` show no
uniform slack above one exists: the proof must be sharp there, not merely
asymptotic.  These rows are builder-owned in the schema-`v2` receipts as
`doubling_plateau_reduction_candidate`.

### The doubled service identity isolates the even-midpoint producer

The companion analysis
`EulerMidpointServiceLaw.md` turns the reduced record inequality into one
local divisor-layer budget.  At a strict record `n=2d-1`, put

\[
 g_d=f(2d)-f(d).
\]

The carry recurrence gives the exact cancellation

\[
 g_d+Q_{2d}
 =2(Q_{2d-1}-Q_{d-1})+Q_d+t_{2d}-t_d.            \tag{EMS-id}
\]

Consequently

\[
 g_d+Q_{2d}\leq2H(d)+t_{2d}-t_d                 \tag{EM}
\]

implies `Q_(2d-1)+1 <= 2H(d)`, hence `(DRMH)` at that plateau start.
This is a strict reduction of the proof surface: the new top 2-adic divisor
layer and the successor reset must be controlled together.  The tempting
split `g_d<=H(d)` is false on the actual orbit at `2d=420`, where
`g_d=6>5=H(d)`.

An exact directed-interval census then destroys the first phase-only
generalisation.  Through rank `2000` and every reduced target of denominator
at most `401`, there are three phase-matched `H(d)>=4` violations, at
midpoints `945`, `195`, and `255`; all three midpoints are odd.  Adding
`2|d` leaves 92,418 rows across 23,951 alive target prefixes, with zero
violations, zero equalities, and minimum margin one.  This selects the open
**even-midpoint service lemma `(EMS)`**: prove `(EM)` when `d` is even,
`t_(2d)=t_d`, and `H(d)>=4`.

For the period-six word of `1/21`, every even `d` automatically satisfies
`t_(2d)=t_d`.  Thus this route consumes only the weaker quarter-phase record
lock

\[
 n+1\equiv0\pmod4,                                \tag{FAPL4}
\]

not the full `(FAPL20)`.  The finite seed through successor `140` is exact,
and `H(80)=4`; `(EMS)+(FAPL4)` therefore covers every later plateau start
and feeds `(DRMH)`.  Neither open lemma is claimed proved.  The exact
experiment, counterexamples, and proof boundary are reproducible with
`scripts/euler_midpoint_service_lab.py`.

The follow-on nested-height experiment sharpens the first open lemma to

\[
 g_d+Q_{2d}\le H(d)+H(d/2)+t_{2d}-t_d.           \tag{NH}
\]

This implies `(EMS)` by monotonicity of `H`.  Across the exact
denominator-at-most-401 survivor census, `(NH)` has zero violations on 92,418
selected rows and 72 equalities, while each of the two natural additive
splits fails twice.  Exact rational gap splices make `(NH)` fail after a
terminal all-take regime begins.  The candidate therefore localizes, rather
than removes, the remaining boundary theorem.  The proof map and executable
countermodels are in
[`NewtonNestedHeightFrontier.md`](NewtonNestedHeightFrontier.md) and
`scripts/newton_nested_height_lab.py`.

### The parity characterization binds exactly to the canonical orbit

The companion note's §16 characterization — `y` survives forever iff
`|x - a/2^n| >= (1/3)·4^{-n}` for every `n` and odd `a`, with `x` the
support word read as a binary number — is bound to the certified canonical
orbit by
[`twenty_one_parity_characterization_binding.py`](../../scripts/twenty_one_parity_characterization_binding.py)
over the immutable packed itinerary.  Exact integer arithmetic through depth
`3000` gives zero survival violations and, more importantly, zero
violations of the exact run bracket that the word algebra predicts:

\[
 3\cdot 2^{\,n-R_n-1}\ \leq\ \mathrm{slack}_n\ <\ 3\cdot 2^{\,n-R_n},
\qquad
 \mathrm{slack}_n := 3\cdot 4^n\,\mathrm{dist}\!\left(x,\ \text{nearest odd } a/2^n\right),
\]

where `R_n` is the maximal run of `1-b_n` starting at position `n+1`.  On
this orbit the Diophantine condition is therefore *exactly* run
combinatorics: death at rank `n` forces `R_n >= n+2`, and survival is the
statement that no forward opposite-run ever reaches length `n+2`.  The
near-edge profile is concentrated early: the minimum slack is `2^2.09` at
`n=6` (forward run `5`), the next four are ranks `1`–`5`, and the slack
profile grows roughly like `2^n` afterward.  The receipt is
`state/formal_math/erdos257_period_noncollapse/twenty_one_parity_characterization_binding_receipt.json`;
it is finite-depth binding of the characterization, not a survival proof.

### Record-edge damping bounds what per-record supply can prove

On a consecutive-record edge `r -> n` exact carry algebra gives

\[
 Q_n+1\ \leq\ 2(Q_r+1)\ -\ \delta_n,
 \qquad \delta_n := 1 + f_n - t_n\ \geq\ 0,
\]

so each record edge carries an explicit damping `delta_n`.  Through two
million ranks there are 39 record edges; 11 have `delta_n = 0`, and every
one of them is an *unselected* take-rank (`b_n = 0`, `t_n = 1`) — prime or
composite, never a selected rank.  Iterating this worst-case edge bound
along each row's halving chain proves only 4 of the 39 reduced rows, with
worst-case chain margin reaching `-1219`.  This is a one-way structural
finding: per-record supply discipline cannot carry `(DRMH)`.  The all-depth
content lives in sustained inter-record divisor-load accumulation — the
windowed sum of `f_k - t_k` with exponential weights between records —
which is where the divisor-density theory of the companion note enters.
The edge table and chain-arithmetic census are builder-owned in the
schema-`v2` receipts as `record_edge_damping_candidate`.

### A fixed rank-19 anchor removes recursive parent search

The source-specific parent clause is simpler than the full weak genealogy.
Every checked strict record after rank `19` satisfies

\[
 n\equiv19\pmod {20}.                              \tag{FAPL20}
\]

Equivalently, the fixed successor `20` divides every later record successor.
Since rank `19` is a weak record with `Q_19=2`, it is therefore one eligible
parent for every later record.  The canonical orbit has 32 such records
through rank `500002` and 37 through rank `2000002`, with no exception.

This is not generic record arithmetic.  In the rational census, the
preselected analogue—use the second strict record as a fixed anchor for all
later strict records—passes on 501 of the 1,557 alive targets and fails on
1,056, with 2,673 exact violating records.  For `1/21`, the second strict
record is exactly rank `19`, its successor is `20`, and all six later records
through the census cap pass.  The much deeper packed receipts extend this to
all 37 later records.

Combining `(FAPL20)` with the weaker edge law `(SEWGN)` also needs no recursive
genealogy.  At a later strict record `n`, use the fixed parent `r=19`.  Then

\[
 Q_n+1
 \leq \frac{n+1}{20}(Q_{19}+1)
 =\frac{3(n+1)}{20}.
\]

There are therefore two nonrecursive theorem routes, not one conjunction:

1. prove `(PMRMH)` for the actual denominator-21 carry; by
   `(PMRMH-linear)` this alone gives the global bound;
2. or prove `(SEWGN)` only on eligible record edges together with the
   source-specific phase lock `(FAPL20)`.

The earlier weak genealogy remains valid finite evidence and supplies exact
falsifiers, but neither route needs to construct or recurse through changing
parents.

This weaker shifted law still has the required one-way consequence.  If a
weak parent `r` lies on the plateau created by strict record `s`, then

\[
 \frac{Q_n+1}{n+1}
 \leq\frac{Q_r+1}{r+1}
 \leq\frac{Q_s+1}{s+1}.
\]

Recursive descent to `(s,Q_s)=(6,1)` yields

\[
 Q_n+1\leq\frac{2(n+1)}7,
\]

again a global linear, hence subexponential, defect bound.  The canonical
census receipt is
`state/formal_math/erdos257_period_noncollapse/rational_weak_record_genealogy_census_receipt.json`.
It stores every target summary, all raw falsifiers, every shifted violation
(the list is empty), the unrestricted multiplicative falsifiers, the
positive-base subcandidate, parentless witnesses, the producer hash, and an
independent `1/21` itinerary binding.  Its schema-`v2` canonical payload digest
is `ce07a64cab489fe1090e960cfb25dfff71a973067a0dcf6f3bbf3367ffe4ca3f`.
This remains finite falsification evidence, not a proof of `(PMRMH)`,
`(SEWGN)`, or parent existence.

## 5. Why the stronger all-depth proof would finish the target

Divisor inclusion gives `f(n+1)>=A(n)`.  Therefore `(AI8)` would imply

\[
 Q_n\leq f(n+1)+8\leq\tau(n+1)+8
\]

at every strict record.  Given any horizon `N`, take the last strict record
`n<=N`.  The defect has not exceeded `Q_n` afterward, so

\[
 Q_N\leq Q_n\leq 2\sqrt{N+1}+8.
\]

This is subexponential.  The existing Lean-checked consumer
`one_div_twenty_one_mem_mersenneAchievementSet_of_defectSubexponential`
then yields membership, including infinite support.  Thus `(AI8)` is a
one-way producer with a completed downstream proof path, not a horizon-only
statistic.

What remains is the all-depth source inequality.  A decisive falsifier is a
strict record whose best inherited load misses its repair bill by more than
eight.  A proof must explain both why suitable record-successor divisors keep
appearing and why their old selected loads remain large enough; divisibility
alone supplies the transfer, not those two facts.

## 6. Reproduction and lineage

The executable source is
[`twenty_one_record_ancestor_inheritance.py`](../../scripts/twenty_one_record_ancestor_inheritance.py).
It consumes the immutable historical exact replay
`twenty_one_computational_structure_receipt_2000002.json`, validates its
canonical payload digest, and records the binding commit and source producer
hash.  It neither replays the greedy orbit nor uses floating point.

The canonical output is
`state/formal_math/erdos257_period_noncollapse/twenty_one_record_ancestor_inheritance_receipt.json`.
The receipt points backward to both motivating analyses and forward to the
Lean consumers of the resulting square-root defect bound.

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/\
  twenty_one_record_ancestor_inheritance.py --write

./repo-python formal_math/erdos257_period_noncollapse/scripts/\
  twenty_one_record_ancestor_inheritance.py --check
```
