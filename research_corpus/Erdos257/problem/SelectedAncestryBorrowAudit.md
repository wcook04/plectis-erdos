# Selected-Ancestry Borrow Audit for Erdős 257

## Status and claim boundary

Erdős problem 257 remains open.  This note does not prove that `1/2` belongs
to the Mersenne achievement set and does not prove universal irrationality.
It records an exact arithmetic conjugacy for the pinned half-greedy orbit and
isolates the only possible first failure.  The first-window divisor charge is
a useful budget coordinate and computation target, but source-current
reconciliation shows that it is exactly the full-shell frozen margin already
formalized in `HalfCylinderFiniteShadow.lean`, not a second producer.

The exact core is Lean-checked in
`ErdosProblems/Erdos257/SelectedAncestryBudget.lean` and the source-current
reconciliation bridge is checked in
`ErdosProblems/Erdos257/SelectedFirstWindowCharge.lean`.  The bounded
structural evidence is produced by
`ErdosProblems/Erdos257/scripts/selected_ancestry_borrow_probe.py` and stored
in
`state/formal_math/erdos257_period_noncollapse/selected_ancestry_borrow_probe_receipt.json`.

## 1. The selected-ancestry budget

Write

\[
 w_n=\frac1{2^n-1},\qquad
 e_n=w_n-2^{-n}=\frac1{2^n(2^n-1)}>0,
\]

and let `r_N` be the exact rational greedy remainder for target `1/2` after
ranks `1,...,N`.  Define the budget recursively by

\[
 B_0=\frac12,
\]

and, at rank `n`,

\[
 B_n=
 \begin{cases}
 B_{n-1}+e_n,&n\text{ is taken},\\
 B_{n-1}-2^{-n},&n\text{ is skipped}.
 \end{cases}
\]

Rank one is skipped, so `B_1=0`.  Direct induction gives the exact identity

\[
 \boxed{r_N=2^{-N}-B_N.}
\]

Equivalently, for the scaled orbit `y_N=2^N r_N`,

\[
 \boxed{y_N=1-2^N B_N.}
\]

Thus the sharpened ceiling `y_N<1` is not another approximate orbit bound:
it is exactly the positivity statement `B_N>0`.

The greedy comparison also becomes

\[
 n\text{ is taken}
 \iff
 B_{n-1}\le 2^{-n}-e_n,
\]

with the strict reverse inequality characterising a skip.

Lean declarations:

- `halfGreedyRemainderRat_eq_dyadic_sub_selectedAncestryBudget`;
- `halfGreedy_take_iff_selectedAncestryBudget_le`;
- `halfGreedy_scaledRat_eq_one_sub_selectedAncestryBudget`;
- `halfGreedy_scaledRat_lt_one_iff_budget_pos`.

## 2. Exact first-crossing law

Suppose `B_n >= 0` but `B_(n+1)<0`.  A take cannot create the crossing,
because it adds the positive amount `e_(n+1)`.  Hence rank `n+1` is skipped.
The skipped-branch inequality gives

\[
 2^{-(n+1)}-e_{n+1}<B_n<2^{-(n+1)},
\]

and therefore

\[
 \boxed{-e_{n+1}<B_{n+1}<0.}
\]

This is Lean-checked as
`halfSelectedAncestryBudgetRat_first_negative_crossing`.  The first possible
failure is consequently a narrow, recoverable negative borrow; broad scalar
escape estimates do not address it.

## 3. Complement target and the factor grid

The complete correction mass after rank one is

\[
 E_*:=\sum_{d\ge2}(w_d-2^{-d}).
\]

Since

\[
 w_d-2^{-d}=\sum_{k\ge2}2^{-kd},
\]

absolute convergence permits regrouping and gives

\[
 \boxed{
 E_*=\sum_{d,k\ge2}2^{-dk}
     =\sum_{n\ge2}(\tau(n)-2)2^{-n}.}
\]

If `A` is a support representing `1/2` and `K={d>=2}\A`, then `K` represents
`E_*`.  In divisor-count notation

\[
 c_K(n)-(\tau(n)-2)=1-c_A(n).
\]

So Booleanising the factor grid is exactly the selected-divisor carry problem
again; the grid reformulation does not remove dependence on the unknown
support.

The most natural support-independent nonlocal carry already fails.  Pair
`(d,k)` with `(k,d)` for `d<k` and use

\[
 2\,2^{-dk}=2^{-(dk-1)}.
\]

This produces the binary coefficient law

\[
 E_*=\sum_{d\ge2}2^{-d^2}
   +\sum_{2\le d<k}2^{-(dk-1)}.
\]

If `C` denotes those binary coefficients and `a=mu*C` is its Möbius inverse,
then exactly

\[
 a_4=a_5=a_7=1,\qquad a_8=-1,\qquad a_9=2.
\]

Thus symmetric factor-pair carrying is non-Boolean by rank nine.  The
distinction between the pair at product six, which the actual orbit must
carry, and the analogous pair at product eight, which it must not carry,
already depends on selected-divisor ancestry.

## 4. The dyadic block is an equivalent frontier, not a shortcut

Define `HalfDyadicBlockHasSkip(N)` to mean that some rank in `(N,2N]` is
skipped.  An eventual supply implies infinitely many skips, hence exact
half-membership; the Lean consumer is
`half_mem_mersenneAchievementSet_of_eventually_dyadicBlockHasSkip`.

However, under the existing open seam-card gap producer, the block statement
is equivalent to the budget sign.  For `N>=8`, assuming
`SeamRemainderCardGapFromEight`,

\[
 \boxed{\operatorname{HalfDyadicBlockHasSkip}(N)\iff B_N\ge0.}
\]

The two directions are:

1. If `B_N<0`, the total future correction deposited before `2N` remains
   below every positive take threshold in that block.  Hence every rank in
   `(N,2N]` is taken.
2. If `B_N>=0` and the entire block is taken, the exact seam coordinate
   `4^N B_N=Phi_N-E_N` lies in the alignment range.  The subset-sum gap
   identifies the actual prefix with the seam greedy word, while the seam-card
   gap forces `E_N>=card(A_N)+2>Phi_N`, a contradiction.

Consequently a proof of the block statement cannot be obtained from the
current seam/card bounds alone: after connection to those bounds, it is the
same missing phase-ceiling sign.

## 5. The first-window charge

Let `A_N` be the actual taken ranks at most `N`, and put

\[
 f_N(m)=\#\{d\in A_N:d\mid m\}.
\]

Let `Q_N` be the integer cell in the exact phase decomposition
`y_N=Q_N-Phi_N`, and define the first old-divisor window

\[
 J_N=\sum_{N<m\le2N}f_N(m)2^{2N-m}.
\]

If every rank in `(N,2N]` is taken, no earlier new block rank can divide a
later one in the same block.  Hence the new contribution at each endpoint is
exactly its own selected bit, and iterating the carry recurrence gives

\[
 \boxed{Q_{2N}=2^N(Q_N-1)+1-J_N.}
\]

Since the remainder is positive, `Q_(2N)>=1`; therefore an all-take block
requires

\[
 J_N\le2^N(Q_N-1).                                      \tag{1}
\]

Selected-divisor ancestry supplies the unconditional lower bound

\[
 J_N\ge\sum_{d\in A_N}2^{N-d},
\]

because every selected `d<=N` has a multiple in `(N,2N]` no later than
`N+d`.  This eliminates the `Q_N=1` sheet, but not the live higher sheets.

The sharply named surviving inequality is therefore

\[
 \boxed{J_N>2^N(Q_N-1)\quad\text{at every actual skipped }N.} \tag{2}
\]

Together with the already formalised fact that an unsafe skip forces the
following dyadic block to be all-take, (2) excludes every unsafe skip and
proves half-membership.  Unlike a fixed phase cap, (2) couples the actual
integer sheet to the first selected-divisor incidence window.

Source-current reconciliation removes a possible double count.  With
`G=greedyMersenneSupport(1/2)`, the existing theorem
`futureSkipCapacity_factorization` gives

\[
 J_N-2^N(Q_N-1)
 =\operatorname{futureSkipCapacity}(G,N,N)
   -\operatorname{mobiusCenteredHalfCarry}(G,2N-1).
\]

Its actual-half specialization is already
`greedyHalfFrozenMargin_eq_actual_skip_margin`, and at the full shell the
left side is exactly `greedyHalfFrozenMargin (N-1) N`.  The existing
`HalfGreedySkippedFullShellNonnegative` consumer therefore owns the all-scale
sign obligation.

`SelectedFirstWindowCharge.lean` adds the missing budget bridge at a skipped
rank:

\[
 \boxed{
 \operatorname{greedyHalfFrozenMargin}(N-1,N)
 =2^{2N}B_N-\Phi_{A_N}(2N).
 }
\]

It also proves that selected-ancestry full-shell tail coverage is equivalent
to `HalfGreedySkippedFullShellNonnegative`.  Thus the budget, charge,
future-skip capacity, frozen margin, and seam sign are exact views of one
producer, not independent routes.

## 6. Exact computation receipt

The receipt replays the pinned half orbit through rank `100000` at `201024`
bits of dyadic precision.  Every branch must be separated by the integer
enclosure; ambiguity aborts.  Divisor pulses, budget signs, block counts, and
window charges use integer arithmetic only.

Observed finite facts:

- `49786` skips and `50214` takes; the last audited skip is `99996`;
- maximum take-run length `16`, at ranks `55128,...,55143`;
- every block `(N,2N]` for `2<=N<=50000` contains a skip;
- `B_N>0` for every audited `2<=N<=100000`;
- the closest dyadic-order approach to `B_N=0` occurs at the skip `N=55127`,
  immediately before the unique length-sixteen take run;
- the logarithmic test window of length `2*ceil(log2 N)` always contains a
  skip on the audited range;
- the first-window inequality (2) holds at every audited skipped `N<=10000`;
  its smallest margin is the exact certificate
  `J_5-2^5(Q_5-1)=39-32=7`.
- the exact capacity factorization agrees at every audited skipped
  `N<=10000`: the same margin is the future-skip binary capacity in
  `(N,2N]` minus the centered carry at `2N`;
- the closest normalized charge margin in that range is at `N=1135`, where
  the positive margin has bit length `1122`, fourteen binary orders below
  `2^N`.  This is the skip immediately before the length-thirteen take run
  `1136,...,1148`.

The tempting stronger shortcut

\[
 \Phi_{A_N}(2N)\ge\frac{2^N}{2^N-1}
\]

is false at exactly 30 audited skipped ranks at most `500`, beginning with
`4,5,8,9` and including `420,432`.  Thus the beyond-block atom tail, a fixed
selected core, or prime coverage alone cannot pay the skip sliver.  Any proof
of (2) must couple `J_N` to `Q_N` and the live skip margin.

A second named shortcut is now excluded.  One might hope that the integer
margin

\[
 M_N=J_N-2^N(Q_N-1)
\]

at skipped ranks occupies a proper low-order residue class, allowing the
full-shell small-packet dichotomy to determine its sign.  An exact replay
through `N=10000` tests all `4994` skipped ranks.  The positive margins occupy
every residue class modulo `2^k` for every `1<=k<=9`, and `1012` of the `1024`
classes modulo `2^10`; both parities occur and the observed `2`-adic valuation
ranges through `13`.  The minimum remains `M_5=7`.

Thus neither a fixed residue nor a bounded valuation class can force (2).
This is a falsifier for the low-order congruence mechanism only, not evidence
against the full-shell sign itself.  The durable authority capture is
`cap_quick_erdos_257_skipped_first_window_margins_h_2bc83d739f8f`.

The suggested last-deposit decomposition is also now discriminated exactly.
Write the old-window charge as a sum over selected denominators,

\[
 J_N=\sum_{d\in A_N}\ \sum_{N<kd\le2N}2^{2N-kd},
\]

and add these contributions in decreasing `d`, so the newest selected
ancestors pay first.  Through `N=2000`, the skipped row `N=1999` needs `979`
selected denominators before the partial charge exceeds `2^N(Q_N-1)` and
reaches back to `d=2`.  Moreover `988` of the `1019` skipped rows are not
certified by even the newest half-width suffix of denominators.

Hence no bounded, logarithmic, or fixed-fraction suffix of recent selected
ancestors can prove the full-shell sign.  A successful ancestry proof must
retain a global ordered telescope across essentially the complete selected
history, or move to the strictly weaker complement-budget boundary of
`SelectedAncestryTailSurvival.lean`.  The durable authority capture is
`cap_quick_erdos_257_recent_selected_ancestors_do_n_264352d15b85`.

That negative result concerns a suffix of **denominators**, not a short
suffix of **endpoint-incidence rows**.  The latter survives a separate named
test.  For a skipped rank `N`, define

\[
 H_{N,L}=\sum_{j=1}^{L} f_N(N+j)2^{L-j}.
\]

Iterating the integer carry for the frozen prefix gives the exact identity

\[
 \operatorname{greedyHalfFrozenMargin}(N-1,L)
   =H_{N,L}-2^L(Q_N-1).                              \tag{3}
\]

Thus the first logarithmic-window crossing

\[
 H_{N,L}\ge 2^L(Q_N-1)                              \tag{4}
\]

is precisely a nonnegative frozen margin, not another approximate
certificate.  Exact replay through `N=10000` finds such an `L` at every one
of the `4994` skipped ranks with

\[
 L\le2\lceil\log_2N\rceil.
\]

The largest observed minimal crossing length is only `15`, at `N=1135`;
just six skipped rows fail the sharper one-binary-length bound, and none
fails the doubled bound.  This is finite evidence, not an all-scale theorem.
Its durable authority capture is
`cap_quick_erdos_257_logarithmic_endpoint_incidence_d3b2f0ec79bf`.

`SelectedFirstWindowCharge.lean` now names the exact all-scale socket
`HalfGreedyLogWindowFrozenMarginProducer` and proves that it implies the
existing governed first-passage producer and hence exact `1/2` membership.
This is materially more local than the full-shell statement: a proof needs
to control only logarithmically many ordered endpoint rows, although each row
still retains divisor ancestry from the complete selected prefix.

The existing logarithmic take-run observation does not prove this producer
by itself.  Through `N=10000`, comparison with the next actual skip gives
`40` crossings before that skip, `786` at it, and `4168` only after it; the
largest observed post-skip delay is four ranks.  Hence the required proof
must control the old-prefix divisor pulses after the first future skip, or an
equivalent coupled capacity/carry potential.  Merely proving that a skip
arrives inside the logarithmic window leaves most audited rows unresolved.
The durable falsifier capture is
`cap_quick_erdos_257_short_take_run_arrival_does_no_2bd3be85984d`.

This coordinate choice is forced by the denominator-cancellation audit, not
just suggested by computation.  The reduced rational remainder retains
uncancellable top-block cyclotomic factors and has genuinely quadratic
denominator height.  The integer recurrence (3) quotients out that height;
trying to sharpen the death-window estimate in the raw remainder coordinate
does not.

All `not_falsified` statements above are bounded evidence only.  The receipt
does not promote them to all-scale theorems.

## 7. Next analytic obligations

The logarithmic first-passage lemma suggested by (3)--(4) is a sharp new
**sufficient** target:

> At an actual half-greedy skip `N`, prove that some
> `L <= 2*ceil(log2 N)` satisfies
> `H_(N,L) >= 2^L * (Q_N - 1)`.

The full-shell inequality remains a valid weaker sufficient target, but (4)
exposes a new scale separation: only `O(log N)` endpoint rows are required.

It is not, however, the weakest exact frontier.  As proved in
`SelectedAncestryTailSurvival.lean`, half-membership is equivalent to

\[
 B_N>-\operatorname{mersenneCorrectionTail}(N)
\]

at every depth.  A narrow negative borrow may therefore be allowed if the
complete correction tail still pays it.  The existing logarithmic
second-shell theorem in `HalfCounterexampleFrontier.lean` applies to the
hypothetical prefix obtained by taking an actual skipped rank, at endpoint
`2N`; its plausible use is to exclude or recover a **fatal** borrow, not to
force the stronger sign `B_N>0` directly.  Connecting that doubled-endpoint
certificate to complement-budget survival is now the weakest analytic seam.

Computation should discriminate named row-by-row potentials or ancestry
telescopes for (4), or a named fatal-borrow transfer from the doubled
second-shell certificate.  It should not extend the orbit horizon without a
proposed lemma.  Any argument that merely rederives future-skip capacity, the
frozen margin, or the seam sign has reached an existing equivalence and must
not be counted as a new producer.
