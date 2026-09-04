# Clean-recovery length counterexample

## Analytic question

The exact reset payments have a subexponential multiplicative upper budget.
Raw negative-run lengths do not force large individual or cumulative reset
payments. A remaining possibility was that the stronger alignment supplied by
a **complete clean recovery** might force its initial payment to grow with the
first-return length.

This probe tests that mechanism directly on the exact primitive rational
cocycle. It does not test lower bounds that also use complete-prefix residues
or arithmetic relations between several recoveries.

## Exact witness

Starting from the primitive pair `(u,v)=(11,362)`, nine exact centered reduced
steps give

```text
u: 11, 3, 4, 5, 6, 7, 8, 9, 10, 11
e:     -1,-1,-1,-1,-1,-1,-1,-1,-1
h:      4, 1, 1, 1, 1, 1, 1, 1, 1
```

The endpoint is the first later height at least 11; all eight interior heights
are strictly below 11. The first payment is nontrivial and every interior
payment is one. This is therefore a `CleanRecoveryAt` interval of length nine,
and `cleanRecovery_payment_eq` identifies its full payment with the initial
factor 4.

Thus both length-only lower bounds fail:

```text
payment = 4 < 9 < 2^9 = 512.
```

No longer computation can restore either universal inequality. Complete
first-return alignment by itself is eliminated as the missing payment lower
bound. A surviving route must consume unbounded prefix gcd/CRT coherence,
relations between several globally coherent recoveries, or further arithmetic
from the original denominator sequence.

## The normalized negative state also returns

The same exact orbit closes a second, structurally different route.  Its
centered error is `-1` at the initial height `u=11`; after the nine-step first
recovery, the height is again `11` and the next exact centered error is again
`-1`.  Hence the normalized negative magnitude returns exactly:

```text
m_start/u_start = 1/11 = m_end/u_end.
```

`CleanRecoveryLengthCounterexample.lean::cleanRecoveryWitness_normalizedNegativeMass_return`
kernel-checks both endpoint states and this rational equality.  This is not
another length estimate.  It eliminates every strict complete-recovery
Lyapunov proposal whose state is only `m/u`: abandoning one-step descent in
favour of sampling at aligned clean recoveries does not repair that coordinate.
Any viable global potential must retain additional changing data such as the
payment, residue class, prime support, or complete-prefix state.

## Reproduction and authority boundary

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos243_clean_recovery_length.py
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos243_clean_recovery_length.py --check
```

The source-bound receipt is
`state/formal_math/erdos257_period_noncollapse/erdos243_clean_recovery_length_receipt.json`.
`CleanRecoveryLengthCounterexample.lean` independently checks the finite
first-return/payment arithmetic and the exact normalized-state return. The
results are one-way mechanism eliminations, not an infinite orbit or a
solution of Erdős #243.

## Infinite congruence family

The normalized return is not an isolated small state. Put

```text
q_0(k) = 33 + 79,833,600 k,
(u_0,v_0) = (11, 11 q_0(k) - 1),       k >= 0.
```

Every member is primitive and follows exactly the same nine-step pattern
displayed above. The proof is a descending congruence certificate, not a
longer orbit audit. On a negative-unit state `(u,uq-1)`, the payment and next
quotient obey

```text
h = gcd(u+1,(q+1)^2),
(u+1)q' = (q+1)(uq-1)+h.
```

If `q` is shifted by `(u+1)Mk`, the right side after division by `u+1`
is unchanged modulo `M`. Starting with the quotient modulus chain

```text
79,833,600, 6,652,800, 1,663,200, 332,640, 55,440,
7,920, 990, 110, 11, 1
```

therefore propagates the required payments
`[4,1,1,1,1,1,1,1,1]` and heights
`[11,3,4,5,6,7,8,9,10,11]` for every `k`. The generic polynomial
propagation is kernel-checked by
`negativeUnitTransitionNumerator_periodic` and
`negativeUnitTransitionQuotient_periodic`; the exact checker validates the
whole gcd and residue chain and independently replays spaced members.

This unbounded family removes two repairs of the failed Lyapunov coordinate:
the return cannot be dismissed as an isolated fixture, and large initial
quotient or denominator does not create strict normalized-mass slack. The
family consists of finite recoveries, not one admissible infinite orbit. A
surviving proof must couple different recoveries through changing complete-
prefix residues, prime support, or cumulative overlap; initial scale alone is
provably invisible to this obstruction.

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos243_infinite_clean_recovery_family.py
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos243_infinite_clean_recovery_family.py --check
```

## The family cannot concatenate itself

The most direct attempt to turn the arithmetic family into one infinite orbit
also has an exact answer.  The descending residue certificate forces the
quotient at height eight to have the form `q_6=990t`.  Writing the last three
negative-unit transitions without division gives

```text
A   = t(7920t+7),                 q_7 = 110A,
B   = A(990A+8) = 2A(495A+4),    q_8 = 11B,
q_9 = B(110B+9).
```

Thus `q_9` is even for every member of the family.  Exact parameter
propagation gives substantially more.  Treating `q_0=33+79,833,600k` as an
integer polynomial and replaying the first six quotient transitions produces
a degree-64 polynomial with

```text
t = q_6/990 = -36 + 1152 c(k),       c(k) in Z[k].
```

This is a coefficientwise identity, not a parameter scan.  Substitution into
the displayed terminal factors yields

```text
q_9 = 41,472 * (2z+1),
q_9 = 41,472  (mod 82,944).
```

The exact checker certifies the source-polynomial divisibility, while
`negativeUnitRecovery_terminalQuotient_oddMultiple_41472` kernel-checks the
small terminal algebra for arbitrary `c`.  Re-entering the same
nine-step congruence cylinder would require

```text
q_9 = 33 + 79,833,600 k',
```

which is always odd.  Direct self-concatenation is therefore impossible for
all parameters.  There is a further one-way constraint.  Since every terminal
quotient is divisible by `12`,

```text
gcd(12,(q_9+1)^2)=1,
u_next=12/1=12.
```

`negativeUnitRecovery_terminal_nextPayment_one` and
`negativeUnitRecovery_terminal_nextHeight_twelve` kernel-check these identities.
Thus no terminal state can switch directly into another height-11 clean
recovery: its first interior height is forced above the return height, whereas
a clean recovery requires every interior height below `11`.  Any infinite
continuation must first control this expanding boundary excursion.

The checker also guards a subtle computational failure mode.  For the tempting
terminal-class sample `q=41472+82944*6`, quotient-only floor division falsely
manufactures a return.  Exact reduced-pair replay follows negative-unit heights
`11,12,13,14,3` and then leaves the negative-unit regime.  Every future cylinder
search must carry the full reduced pair or assert exact quotient divisibility
at every step.

## The forced excursion splits at height twelve

Carrying the *source parameter* is substantially stronger than sampling an
arbitrary representative of the terminal class.  Starting from

```text
q_0(k) = 33 + 79,833,600 k
```

the ten exact negative-unit quotient transitions produce an integer
polynomial `q_10(k)` of degree `1024`.  Reducing `q_10(k)+1` as a polynomial
function on `F_13` gives, with coefficients written from low to high,

```text
[0,0,1,4,2,3,9,12,8,7,7,7,7].
```

The checker verifies the complete factorization

```text
7 x^2 (x-2)^2 (x-5) (x-6)^2 (x-7) (x-8)
  (x-9)^2 (x-10)                         in F_13[x].
```

Consequently the height-12 payment is the full factor `13` exactly when

```text
k mod 13 in {0,2,5,6,7,8,9,10}.
```

For every nonnegative lift of any of these eight classes, the primitive
height collapses from `12` to `1`.  A primitive rational state with numerator
one is integral, so its centered error is zero and the exact cocycle remains
on the Sylvester tail forever.  This is an infinite union of exact cofinal-
return subfamilies, not a representative search.  Only

```text
k mod 13 in {1,3,4,11,12}
```

survives to height `13`.  Thus any attempt to construct infinite negative
support inside the normalized-return family must live in those five classes;
the other eight are closed permanently.  The next useful computation is a
residue-cylinder split restricted to those survivors, not a longer audit of
arbitrary parameters.

`negativeUnitRecovery_heightTwelve_fullPayment` and
`negativeUnitRecovery_heightTwelve_collapse` kernel-check the generic small
divisibility consumer.  The source-polynomial propagation and finite-field
factorization are certified by
`scripts/check_erdos243_forced_excursion_split.py`, with the durable receipt at
`state/formal_math/erdos257_period_noncollapse/erdos243_forced_excursion_split_receipt.json`.

## The second split: four more cofinal-return classes

The five classes surviving height twelve separate into two genuinely
different centered branches.  For

```text
k mod 13 in {3,4,11,12},
```

the height-13 centered error remains `-1`.  Writing `k=r+13t`, exact quotient
propagation modulo `13*14` shows that the next multiplier is always `1` or `7`
modulo `14`.  Hence the payment is exactly `1` or `7`, never the full factor
`14`.  The immediate full-payment route to height one is therefore eliminated
on all four branches.  The payment-seven subcylinders land at the centered
boundary `(u,e)=(2,-1)`; they must be analyzed separately from the payment-one
height-14 subcylinders rather than merged into one nominal excursion.

The remaining source class behaves differently.  Put

```text
k = 1 + 13t.
```

At height `13` its centered error is `-4`, so the possible full payment is
`13-(-4)=17`.  Propagating the centered quotient numerator modulo `13*17`,
then dividing coefficientwise by `13`, gives

```text
payment 17  iff  t mod 17 in {8,9,13,14},
            iff  k mod 221 in {105,118,170,183}.
```

Every lift in these four classes collapses to primitive height one and enters
centered state zero forever.  Together with the first height-12 split, exactly
`140` of the `221` source classes modulo `221` are now forced into a cofinal
Sylvester return.  The same residue table also determines the complements:
the seven classes where the next multiplier is `5 mod 17` land at height `17`
with centered error `+2`, and the six classes where it is `13 mod 17` land
with centered error `+4`.  Thus the entire `k=1 mod 13` branch either returns
to zero or switches sign; none continues negative support.  The exact
three-way partition modulo `221` is

```text
140 zero-centered + 13 positive-centered + 68 continuing-negative candidates.
```

Only the four negative-unit source classes can still carry the expanding
negative mode.  This does not settle their later dynamics or unrestricted
Erdős #243.

The computation uses a reusable exact-division device.  If an integer
polynomial `N` is coefficientwise divisible by `d`, then `N mod (dM)` recovers
`(N/d) mod M` exactly.  The shared implementation in
`system/lib/formal_math_residue_cylinder.py` avoids materializing the next
degree-2048 giant integer polynomial while retaining a proof-grade finite
residue certificate.  The exact problem-specific checker is
`scripts/check_erdos243_second_excursion_split.py`; its receipt is
`state/formal_math/erdos257_period_noncollapse/erdos243_second_excursion_split_receipt.json`.
The generic small arithmetic consumers are kernel-checked as
`negativeFourHeightThirteen_fullPayment` and
`negativeFourHeightThirteen_collapse`.

## Payment seven forces a cofinal return

The payment-seven height-two boundary is not a surviving mechanism.  The
composite-modulus cylinder can be sharpened from modulo `14` to modulo `42`:
on all sixteen payment-seven source classes modulo `182`, the height-13
multiplier satisfies

```text
a_13 = q_13 + 1 = 7 (mod 42).
```

Write `a_13=7w` with `w=6z+1`.  After payment seven the height is two and the
new denominator coordinate is

```text
v_2 = 7w(13w-2) = 6m-1,
m   = 546z^2 + 168z + 13.
```

Thus the height-two state is the exact centered tie `(u,e)=(2,-1)`, with
quotient `q_2=3m`.  Its multiplier is `3m+1`, so the payment is one and the
next height is three.  The next denominator is

```text
(3m+1)(6m-1) = 3(6m^2+m)-1.
```

Hence the height-three error is again `-1`.  Since `m` is odd, the next
multiplier `6m^2+m+1` is even; its square is divisible by four, so the dynamic
payment is the full factor `4` and the primitive height collapses to one.
The exact cascade is therefore

```text
(13,-1) --h=7--> (2,-1 tie) --h=1--> (3,-1)
        --h=4--> (1,0 forever).
```

This quantifies over every lift in all sixteen cylinders, rather than a longer
sample trace.  On the common modulus `3094=13*14*17`, the clean-return family
now has the exact partition

```text
2232 zero-centered + 182 positive-centered
  + 680 continuing-negative candidates.
```

The payment-seven boundary mode is closed.  Only the payment-one height-14
cylinders over `k mod 13 in {3,4,11,12}` remain eligible for continuing
negative support.  `scripts/check_erdos243_payment_seven_cascade.py` owns the
residue and replay certificate, while
`paymentSevenCascade_finalFullPayment` and
`paymentSevenCascade_finalCollapse` kernel-check the final generic payment.

## Payment one splits at height fourteen

The remaining forty cylinders modulo `182` all reach height `14` with
centered error `-1`.  If the preceding height-13 multiplier is written

```text
A = q_11 + 1 = 14w + 1,
```

then the height-14 multiplier is the exact quadratic

```text
B = q_14 + 1 = 182w^2 + 12w + 1.
```

Generic modular algebra permits several images of `w mod 15`, including
classes where the payment would be the full factor `15`.  Those classes are
not realized by the actual source family.  Composite-modulus propagation of
the degree-1024 source polynomial, followed by exact division first by `13`
and then by `14`, proves on all forty cylinders that

```text
w mod 15 in {0,3}.
```

Refining each cylinder by its fifteen parameter lifts gives exactly 600
classes modulo `2730`.  The two images have different one-way consequences.

For `w=15z+3`, the multiplier `B` is five times
`C=3d+2`, where `d=2730z^2+1104z+111`.  After payment five, the new height is
three and

```text
v_3 = 5C(14C-3) = 3(210d^2+265d+83)+1.
```

Thus the centered error is `+1`.  All 240 such classes switch sign and cannot
continue the expanding negative boundary mode.

For `w=15c`, the payment at height 14 is one.  Writing

```text
m = 2730c^2+12c,
D = q_15+1 = 210m^2+13m+1,
```

shows that `m` is even, so `D` is odd and the height-15 payment is also one.
Moreover `D^2=1 mod 16`: for even `c`, `D=1 mod 8`, and for odd `c`,
`D=-1 mod 8`.  Hence these 360 classes reach height `16` with centered error
`-1`.  This is now the only surviving negative-support branch in the known
clean-return family.

On the common modulus `46410=13*14*15*17`, the cumulative exact partition is

```text
33480 zero-centered + 6810 positive-centered
  + 6120 continuing-negative candidates.
```

This is a structural split, not a horizon extension.  The next discriminating
object is the height-16 multiplier modulo `17`; a full payment, sign switch,
or new finite residue image there is the next legitimate stopping event.
`scripts/check_erdos243_payment_one_height14.py` owns the exact polynomial
certificate and durable receipt.  The identities
`paymentOneHeightFourteen_positiveSwitchIdentity`,
`paymentOneHeightSixteen_evenLiftSquare`, and
`paymentOneHeightSixteen_oddLiftSquare` are the Lean arithmetic consumers.

## Height sixteen closes most of the remaining cylinders

The 360 height-16 survivors refine into 6120 complete residue cylinders on
the already natural modulus

```text
46410 = 13*14*15*17.
```

The exact degree-1024 source polynomial need not be affine-expanded again.
Its coefficients are reduced once modulo `46410`, then evaluated on every
residue cylinder.  Pointwise exact division recovers the successive quotients
modulo `14*15*17`, `15*17`, and `17`.  This produces the unexpectedly rigid
image

```text
c mod 17 in {0,10,12}.
```

If `D=210m^2+13m+1` is the height-15 multiplier, then the height-16
multiplier is

```text
E = (15D^2-16D+17)/16 = 2D^2-D (mod 17).
```

The three actual parameter images give exactly:

```text
c = 12: E = 0 mod 17, payment 17, height 1, centered zero  (1440 classes)
c = 10: E = 3 mod 17, payment  1, height 17, error +8      (2520 classes)
c =  0: E = 1 mod 17, payment  1, height 17, error -1      (2160 classes)
```

Thus 1440 further cylinders make a cofinal return and 2520 lose negative
support by a sign switch.  Only the `c=0 mod 17` image survives.  The entire
known clean-return family now has the exact partition

```text
34920 zero-centered + 9330 positive-centered
  + 2160 continuing-negative candidates = 46410.
```

`scripts/check_erdos243_height16_mod17.py` owns this certificate.  It also
uses the shared pointwise primitive `exact_quotient_value_mod`, which avoids
large substituted-polynomial expansion whenever a complete finite cylinder
is already being enumerated.  The Lean consumers are
`paymentOneHeightSixteen_fullPayment`,
`paymentOneHeightSixteen_fullCollapse`,
`paymentOneHeightSixteen_positiveSwitchIdentity`, and
`paymentOneHeightSixteen_negativeSurvivorIdentity`.

The only legitimate next family-specific probe is the transition out of the
exact multiplier-one height-17 survivors.  Collapse and positive classes are
terminal for negative-support analysis and must not be audited further.

## Height seventeen is rigid; height eighteen returns cofinally

The 2160 multiplier-one height-17 classes first refine modulo four.  Exact
division of the source quotient on all `2160*4=8640` lifts gives the singleton
image

```text
d mod 4 = 0.
```

Generic height-17 algebra would allow payments `18`, `9`, `2`, or `1`.
The actual family realizes only payment one.  Writing `d=4e` makes the next
parameter `z` a multiple of six, say `z=6y`, and the height-17 multiplier is

```text
F = 272z^2+15z+1 = 18(544y^2+5y)+1.
```

Thus every lift reaches height `18` with centered error `-1`; the nontrivial
height-17 cancellation mechanism is eliminated exactly.

The substitution also makes `y` an integer polynomial of degree eight in
`e`.  The current modulus `185640` is coprime to `19`, so the nineteen lifts
of every source cylinder traverse every residue in `F_19`.  Combining the
degree-1024 source polynomial with the degree-eight quotient identity gives

```text
e mod 19 in {0,2,15},
y mod 19 in {0,9,15},
G mod 19 in {0,1},
```

where

```text
G = q_18+1 = 306m^2+16m+1,
m = 544y^2+5y.
```

The complete source-class split is

```text
G = 0 mod 19 on k mod 19 in {1,3,4,7,8,10,11,13,14,17,18};
G = 1 mod 19 on k mod 19 in {0,2,5,6,9,12,15,16}.
```

The first eleven classes pay the full factor `19`, collapse to height one,
and enter the absorbing centered-zero tail.  The other eight pay one and
retain error `-1` at height `19`.  No positive branch occurs.  On the common
modulus `3527160=185640*19`, the cumulative exact partition is

```text
2748960 zero-centered + 709080 positive-centered
  + 69120 continuing-negative candidates.
```

`scripts/check_erdos243_height17_mod4.py` owns the combined mod-4 rigidity and
mod-19 cofinal-return certificate.  The Lean consumers are
`paymentOneHeightSeventeen_paymentOne`,
`paymentOneHeightEighteen_fullPayment`,
`paymentOneHeightEighteen_fullCollapse`, and
`paymentOneHeightEighteen_negativeSurvivorIdentity`.  Future family-specific
work must restrict to the eight multiplier-one height-19 classes; the eleven
cofinal-return classes are closed permanently.

## Payment five at height nineteen also forces a return

The eight multiplier-one height-19 residue classes refine by ten.  This is a
large but finite exact cylinder: `69120*10=691200` source classes modulo
`35271600`.  The checker pre-reduces every coefficient of the exact
degree-1024 source polynomial, then evaluates all classes with integer-only
NumPy Horner arithmetic.  The largest nonlinear intermediate is bounded by
`12*35271600^2`, strictly below `2^63`; no floating-point arithmetic or
probabilistic residue sampling is used.

Successive exact divisions recover the next source parameter.  Its complete
image and counts are

```text
t mod 10 :  0       2      4      6      8
count    : 322560  92160  92160  92160  92160.
```

The next integer-polynomial parameter satisfies `s=t mod 10`.  Consequently
the height-19 multiplier image modulo `20` is only

```text
H = 5 mod 20  for t in {2,8}: 184320 classes, payment 5;
H = 1 mod 20  for t in {0,4,6}: 506880 classes, payment 1.
```

Payments `20` and `4` never occur.  The payment-five branch is nevertheless
terminal.  Write `H=5W` with `W=4b+1` and put

```text
X = 76b^2+34b+4.
```

After payment five, the new height is four and its denominator satisfies

```text
5W(19W-4) = 4(5X-1)-1.
```

Thus the centered error is `-1` and the next multiplier is `5X`.  Its square
pays the full factor five, collapsing the primitive height to one.  Every one
of the 184320 payment-five cylinders therefore makes a cofinal return.  Only
the payment-one classes reach height `20` with centered error `-1`.

The cumulative exact partition is now

```text
27673920 zero-centered + 7090800 positive-centered
  + 506880 continuing-negative candidates = 35271600.
```

`scripts/check_erdos243_height19_payment_five_cascade.py` owns the complete
vectorized cylinder, branch digests, exactness bounds, and symbolic cascade.
The Lean consumers are
`paymentFiveHeightNineteen_heightFourIdentity`,
`paymentFiveHeightNineteen_finalFullPayment`, and
`paymentFiveHeightNineteen_finalCollapse`.  The next probe must discard the
payment-five classes and restrict to `t mod 10 in {0,4,6}` at height 20.

## Payment seven at height twenty cannot carry negative support

The 506880 payment-one height-20 cylinders refine by twenty-one.  Expanding
the degree-1024 source polynomial separately on all 10644480 lifts would be
needlessly expensive: exact evaluation at lift zero and lift one determines
the higher coordinate affinely modulo both `21` and `5`.  CRT then recovers
the required quotient digit modulo `105`.  The complete height-20 image is

```text
payment 1 : 8211456 classes
payment 7 : 2433024 classes
payment 3 or 21 : no classes.
```

The affine certificate is itself inspectable.  The lift slope modulo `21`
has the uniform five-value image

```text
0, 3, 9, 12, 18 : 101376 source cylinders each,
```

and the multiplier parameter has image and counts

```text
p mod 21 :    0        12       18
count    : 3345408  4866048  2433024.
```

Only `p=18 mod 21` pays seven.  Write `p=21a+18`; the next quotient digit
modulo five has the exact split

```text
a mod 5 :      0       1        2       3       4
count   :  176960  176953  1725225  176949  176937.
```

Every one of these five branches is decided by a complete symbolic residue
period, not a finite orbit horizon.  Writing `W=6c+1`, payment seven gives

```text
7W(20W-3) = 3(1680c^2+518c+40)-1,
```

so every branch lands at height three with centered error `-1`.  After its
forced payment one at heights three and four:

- digits `a=0,1` make the height-four multiplier divisible by five, hence
  pay the full factor five and return to height one;
- digit `a=3` has multiplier `3 mod 5`, so the height-four payment-one step
  switches to centered error `+1` at height five;
- digits `a=2,4` reach height five with a multiplier `3 mod 6`, pay three,
  land at height two with a multiplier divisible by three, and return to
  height one.

Thus all 2433024 payment-seven cylinders are terminal for negative support:
2256075 make a cofinal return and 176949 switch positive.  Only the 8211456
payment-one cylinders reach height `21` with centered error `-1`.  On the
common modulus `740703600=35271600*21`, the cumulative exact partition is

```text
583408395 zero-centered + 149083749 positive-centered
  + 8211456 continuing-negative candidates = 740703600.
```

`scripts/check_erdos243_height20_payment_seven_cascade.py` owns the affine
two-lift/CRT cylinder certificate, exact counts, int64 safety bound, and
complete symbolic cascade.  Its affine compression is the first consumer of
the shared `formal_math_residue_cylinder.affine_lift_coordinates_mod`
primitive, so the computation-to-analysis link is reusable by later problem
cylinders rather than trapped in this checker.  The Lean consumers are
`heightTwentyPaymentSeven_heightThreeIdentity`,
`heightTwentyPaymentSeven_positiveSwitchIdentity`,
`heightTwentyPaymentSeven_heightFiveToHeightTwoIdentity`,
`heightTwentyPaymentSeven_finalFullPayment`, and
`heightTwentyPaymentSeven_finalCollapse`.  Future family-specific work must
discard payment seven and restrict to the height-21 payment-one cylinder.

## Height twenty-one forces a height-three cofinal return

The 8211456 surviving height-20 classes refine by twenty-two.  The same
affine-lift primitive recovers their higher quotient coordinate from lift zero
and lift one, classifying all 180652032 refined classes.  If `r` denotes the
divided height-20 quotient parameter, the height-21 multiplier is

```text
L = 420r^2+19r+1.
```

Although a generic residue can realize payments `1`, `2`, `11`, or `22`, the
actual source image is the two-point set

```text
r mod 22 :       0          6
count    : 120931560   59720472
L mod 22 :       1         11
payment  :       1         11.
```

Thus payments two and twenty-two are absent.  The payment-one classes reach
height `22` with centered error `-1`.  On the payment-eleven class write
`r=22a+6` and

```text
B = 9240a^2+5059a+692,
W = L/11 = 2B+1.
```

After payment eleven the exact transition is

```text
W(231W-22) = 2(462B^2+440B+105)-1,
```

so it lands at height two with centered error `-1`.  A three-lift refinement
should generically allow either payment one or full payment three there.  The
actual degree-1024 source cylinder is again rigid:

```text
r mod 66 = 6                    on all 179161416 refined classes,
W mod 3 = 2                    on all 179161416 refined classes,
height-two multiplier mod 3 = 1 on all 179161416 refined classes.
```

Consequently full payment three never occurs.  Every payment-eleven lift pays
one at height two and reaches height three with centered error `-1`; its actual
height-two multiplier is `1 mod 6`, so write it as `3c+1` with `c=2z`.  Then

```text
(3c+1)(2(3c+1)-3) = 3(6c^2+c)-1.
6c^2+c = 2(12z^2+z).
```

The height-three multiplier is therefore even, its square pays the full factor
four, and every payment-eleven class collapses to height one.  This is a
one-way cofinal-return result rather than a longer-horizon audit: the candidate
return at height two is absent, but the stronger forced return one step later
closes the entire payment-eleven mode.  On the common modulus
`48886437600=740703600*22*3`, the cumulative partition is

```text
38684115486 zero-centered + 9839527434 positive-centered
  + 362794680 continuing-negative candidates = 48886437600,
```

and every continuing-negative class is in the height-twenty-two payment-one
branch.  The owner is
`scripts/check_erdos243_height21_payment_split.py`; its Lean consumers are
`heightTwentyOne_paymentOne`,
`heightTwentyOnePaymentEleven_heightTwoIdentity`,
`heightTwentyOnePaymentEleven_heightThreeIdentity`,
`heightTwentyOnePaymentEleven_heightThreeMultiplierEven`,
`heightTwentyOnePaymentEleven_fullPaymentFour`, and
`heightTwentyOnePaymentEleven_finalCollapse`.  The next exact probe must
discard payment eleven and restrict to the `362794680` height-twenty-two
payment-one classes.

## Height twenty-two has a compressed centered-state split

Before carrying the common factor-three refinement, the sole height-22 branch
has `120931560` source families modulo `16295479200`.  A literal refinement by
twenty-three would materialize `2781425880` classes.  The checker instead
recovers the higher coordinate modulo `23` at lift zero and lift one and then
counts every multiplier-residue fiber over the complete affine period.

Write the height-21 multiplier as `22q+1`.  Payment one gives

```text
(22q+1)(21(22q+1)-22) = 22((462q^2+20q+1)-1)-1,
```

so the height-22 multiplier is `R=462q^2+20q+1`.  If `r=22s` is the preceding
quotient parameter, then `q=9240s^2+19s`.  Exact finite-field algebra gives

```text
R = 0 mod 23  exactly when  s mod 23 is 11 or 19;
q = 12 mod 23 on both roots.
```

The complete multiplier image is not merely classified by payment:

```text
R mod 23 :   0   1  15
new error:   0  -1  +5
```

Indeed, after payment one the reduced numerator has centered residue
`-R^2 mod 23`.  Thus residue fifteen is positive, not a continuing negative
state.  The exact transition identities are

```text
(23z+15)(22(23z+15)-23) = 23(506z^2+637z+200)+5,
(23z+ 1)(22(23z+ 1)-23) = 23(506z^2+ 21z)-1.
```

Each actual source category has respectively ten, nine, and four higher
coordinates mapping to residues zero, one, and fifteen.  The lift slope
distribution is

```text
slope 0 : 99902640 source families
slope 7 :  5266398
slope 11:  5250828
slope 12:  5249736
slope 16:  5261958.
```

Every nonzero slope traverses all of `F_23`, hence contributes exactly
`10/9/4` lifts to residues `0/1/15`.  A zero slope contributes all twenty-three
lifts to one residue.  The exact source-family splits by number of lifts are

```text
R=0 :  21045114 families contribute 0, 21028920 contribute 10,
       78857526 contribute 23;
R=1 :  78857526 families contribute 0, 21028920 contribute 9,
       21045114 contribute 23;
R=15:  99902640 families contribute 0, 21028920 contribute 4.
```

Therefore the complete height-22 centered-state partition is

```text
payment 23 and cofinal return : 2024012298 classes,
payment 1 and error +5        :   84115680 classes,
payment 1 and error -1        :  673297902 classes.
```

This is exact residue-fiber counting, not sampling and not an orbit horizon.
It corrects the tempting but false inference that payment one automatically
preserves centered error `-1`.  The
shared `affine_full_lift_acceptance_table` primitive proves the fiber count for
prime or composite moduli using `gcd(slope, modulus)`, so later problem probes
can avoid similarly explosive lift expansions.  The shared
`negative_unit_successor_signature` primitive separately derives payment,
next height, and the tie-correct centered error, preventing payment-only
classifiers from silently preserving the wrong sign.  Restoring the common
factor-three refinement, the cumulative partition on modulus
`1124388064800=48886437600*23` is

```text
895806693072 zero-centered + 226561478022 positive-centered
  + 2019893706 continuing-negative candidates = 1124388064800.
```

All continuing-negative classes are height-23 multiplier-residue-one classes.
The owner is `scripts/check_erdos243_height22_mod23_split.py`; the Lean consumers are
`heightTwentyTwo_transitionIdentity`,
`heightTwentyTwo_sourceRootIdentity`,
`heightTwentyTwo_multiplierAtTwelveIdentity`,
`heightTwentyTwo_fullPayment`, `heightTwentyTwo_fullCollapse`,
`heightTwentyTwo_positiveSwitchIdentity`, and
`heightTwentyTwo_negativeSurvivorIdentity`.  Future family-specific work must
discard every full-payment and residue-fifteen class and restrict to the true
height-23 negative survivors.

## Height twenty-three has only the multiplier-one mode

The corrected height-22 split leaves `673297902` negative classes before the
common factor-three lift.  A literal factor-24 refinement would create
`16159149648` classes.  The exact checker instead compresses the `506880`
source families to `6699` joint affine keys modulo `21,22,23,16,9`, then to
only `570` weighted height-22 state keys.

Factor `24` overlaps the preceding product, so coprime CRT is insufficient.
The checker reconstructs the height-19 source parameter from its compatible
residues modulo `10626`, `16`, and `9`; generalized CRT gives the exact modulus

```text
lcm(10626,16,9) = 255024.
```

For a height-22 residue-one survivor, write its multiplier as `23z+1`.  The
height-23 multiplier is

```text
A = 506z^2+21z+1.
```

Generic `z mod 24` permits six successor modes: payments `1,3,4,8,12,24`,
including full collapse and a positive switch.  The actual source image is
the singleton

```text
z mod 24 = 0,
A mod 24 = 1
```

on all `16159149648` logical refinements.  Thus all five nontrivial generic
modes are absent: no height-23 class returns cofinally, switches positive, or
lands at height `2`, `3`, `6`, or `8`.  Every class pays one and reaches height
`24` with centered error `-1`.  This is a complete mechanism elimination, not
a longer orbit horizon.

The cumulative partition on modulus
`26985313555200=1124388064800*24` is

```text
21499360633728 zero-centered + 5437475472528 positive-centered
  + 48477448944 continuing-negative candidates = 26985313555200.
```

`scripts/check_erdos243_height23_composite_split.py` owns the weighted-key
census, overlapping-CRT reconstruction, exact mode counts, and experiment
contract.  The Lean consumers are
`heightTwentyThree_actualMultiplierOneIdentity` and
`heightTwentyThree_negativeSurvivorIdentity`.  Future family-specific work
must restrict to this singleton height-24 mode and test the new factor `25`
rather than revisit the five eliminated factor-24 branches.

## Factor twenty-five opens an actual cofinal return

Write the actual height-23 multiplier as `24c+1`.  The height-24 multiplier is

```text
B = 552c^2+22c+1.
```

Generic `c mod 25` permits payment one or full payment twenty-five.  The full
payment roots are exactly `c mod 5 in {1,3}` because

```text
B - 2(c-1)(c-3) = 5(110c^2+6c-1).
```

The preceding quotient `w` satisfies `c=12144w^2+21w`, hence
`c=w(1-w) mod 5`.  Only the root `c=3 mod 5` is reachable, exactly from
`w mod 5 in {2,4}`.  The Lean identities
`heightTwentyFour_precedingQuotientTwoIdentity`,
`heightTwentyFour_precedingQuotientFourIdentity`, and
`heightTwentyFour_multiplierAtThreeModFiveIdentity` bind this analytic route;
`heightTwentyFour_fullPayment` and `heightTwentyFour_fullCollapse` certify the
cofinal consequence.

The complete exact source reconstruction works modulo

```text
255024*25 = 6375600.
```

It compresses the source to `166140` joint affine keys and `32490` weighted
height-22 keys, then classifies all `403978741200` logical refinements.  The
actual preceding-quotient image is even narrower than the generic root
calculation:

```text
w=0                                      : 286453354320
w in {1,4,6,9,11,14,16,19,21,24}, each  :  11752538688
```

Hence `w mod 5` is only `{0,1,4}`.  The possible cofinal root `w=2 mod 5` is
absent, while every realized `w=4 mod 5` class forces the root `c=3 mod 5`.
The resulting actual `c mod 25` counts are

```text
c=0                                      : 298205893008
c in {3,5,8,10,13,15,18,20,23}, each    :  11752538688
```

Thus the actual factor-25 outcome is

```text
payment 25, height 1, cofinal return     :  58762693440
payment 1, positive error +4 or +9       :  23505077376
payment 1, negative error -1,-6,or -11   : 321710970384
```

This is a one-way mechanism opening: actual source classes, rather than merely
generic residues, force a cofinal return.  It also eliminates the generic
error `-9` mode and removes `82267770816` classes from negative support.  In exact
counts the removal is `82267770816 = 58762693440+23505077376`, or about
`20.364%` of the incoming factor-25 cylinder.  The surviving negative share is
`321710970384/403978741200`, about `79.636%`.  The analytic route this opens is
not blind continuation to factor 26: test whether the affine-fiber geometry
forces a uniform subunit continuation fraction across subsequent factors.
Such a bound would kill the expanding homogeneous boundary mode by geometric
mass loss.

Restoring the common factor-three refinement gives the cumulative partition
on modulus `674632838880000=26985313555200*25`:

```text
537660303923520 zero-centered + 136007402045328 positive-centered
  + 965132911152 continuing-negative candidates = 674632838880000.
```

`scripts/check_erdos243_height24_mod25_split.py` owns the exact census and its
experiment contract.  Its digest-bound compressed affine cache stores only
the `32490` weighted keys, rejects source drift, and makes later receipt checks
reuse the expensive degree-1024 source propagation without treating the cache
as mathematical authority.

## Factor-twenty-five loss is a binary fiber phenomenon

The aggregate `20.364%` removal does **not** give a uniform contraction on
each height-24 parent.  Retaining parent identity across the complete set of
25 refinements produces exactly two profiles:

```text
cofinal 0, positive 0, negative 25 : 10282880304 parents
cofinal 10, positive 4, negative 11:  5876269344 parents
```

The totals recover the independent child census exactly:

```text
10*5876269344 = 58762693440 cofinal children,
 4*5876269344 = 23505077376 positive children,
25*10282880304 + 11*5876269344 = 321710970384 negative children.
```

Thus `10282880304` actual parents have continuation ratio `1`, decisively
eliminating the proposed uniform one-step bound.  But the failure is rigid,
not diffuse: every non-inert parent removes exactly `14/25` of its children
from negative support.

Crossing the profiles with the retained height-19 source digit gives an exact
and unexpectedly simple separator:

```text
t mod 10 = 0      if and only if the parent is inert,
t mod 10 in {4,6} if and only if the parent is active.
```

Affine slopes `3` and `7` occur on both sides, while slopes divisible by five
occur only on the inert side; slope alone is therefore not the activation
cause.  The replacement analytic route is now sharper than generic recurrence:
restrict computation to the exact `t=0` inert subfamily and find the next new
prime/residue or derivative that activates it.  The already active `t=4,6`
branches need no further rediscovery.  A bounded-gap or positive-density
activation theorem for the successive inert subfamilies would convert the
`11/25` active continuation ratio into geometric mass loss without pretending
that every single factor contracts.

`scripts/check_erdos243_height24_parent_contraction.py` owns the exact weighted
parent-profile histogram and its experiment contract.  It reuses the
source-current compressed affine cache but recomputes every factor-25 child
classification; the cache is acceleration only.

The child error image removes another apparent branching cost.  On the inert
source digit the complete negative image is

```text
t=0, centered error -1: 257072007600 children,
t=0, centered errors -6 or -11: 0 children.
```

The `-6` and `-11` modes occur only under the already-active digits `4` and
`6`.  Therefore the inert continuation has raw next-height factor only
`25-(-1)=26`; the candidate factors `31` and `36` are eliminated from this
frontier.  Exact source extension should compute only the additional prime
powers `32` and `13` needed to refine the current source modulus by 26.

## Factor twenty-six uniformly activates every inert fiber

The apparent source extension from `6375600` to `165765600=6375600*26`
contains a useful compression.  The new quotient has one bit modulo `32` and
one coordinate modulo `13`.  On actual parent support, exact comparison of
the two possible quotient parities gives the same sorted multiplier-residue
multiset.  Each parity class contains thirteen distinct target residues, so
the complete 26-lift profile is two copies of either class.  The unordered
parent census can therefore reuse the existing 32490-key factor-25 cache
instead of materializing the larger affine cylinder.

Only eighteen current-modulus parent residues occur.  Nevertheless all
`257072007600` logical inert children have exactly the same factor-26 profile:

```text
cofinal 0, positive 4, continuing negative 22 : 257072007600 parents
```

More sharply, every parent has the multiplier multiset

```text
C mod 26 = 1^8, 13^14, 15^4.
```

The corresponding successor modes are

```text
C=1  : payment 1,  height 26, centered error -1 : 8 children
C=13 : payment 13, height 2,  centered error -1 : 14 children
C=15 : payment 1,  height 26, centered error +9 : 4 children.
```

Thus no all-negative parent survives even at the immediate factor-26 step.
There is a stronger forced cascade.  On the fourteen `C=13` children the
payment is thirteen, so the reduced multiplier is `W=C/13=1`.  The exact
height-two multiplier is

```text
(W(25*13*W-26)+1)/2 = 150.
```

Its square pays the full factor three, collapses to height one, and returns
cofinally.  The effective profile after this forced step is therefore

```text
cofinal 14, positive 4, continuing negative 8 : every parent.
```

The previously inert boundary retains only `8/26=4/13` in genuine negative
support.  This eliminates the all-negative fiber mode at the first factor
after the failed factor-25 one-step contraction, but the eight multiplier-one
children still carry the expanding negative boundary and require the next
distinct factor-27 probe.  Across the two-factor block, an active height-24
parent already retains only `11/25`, while an inert parent retains `4/13`;
hence `11/25` is a uniform upper bound for the block.

The absence of factor-26 cofinal return is analytic, not merely empirical.
For the preceding multiplier

```text
B = 552c^2+22c+1
```

we have `B` odd.  If the next multiplier is defined by

```text
25C = 24B^2-25B+26,
```

then reduction modulo two gives `C` odd.  Consequently `26` cannot divide
`C^2`, so full factor-26 payment is impossible.  Lean declarations
`heightTwentyFive_multiplierOdd` and
`heightTwentyFive_noFullPaymentDivisibility` bind this obstruction.  The
declarations `heightTwentyFivePaymentThirteen_heightTwoMultiplier`,
`heightTwentyFivePaymentThirteen_fullPaymentThree`, and
`heightTwentyFivePaymentThirteen_finalCollapse` bind the forced return one
step later.  The exact census then supplies the stronger source-specific
uniform profile.

`scripts/check_erdos243_t0_factor26_activation.py` owns the compressed parent
cache, parity-invariance comparison, exact weighted census, and experiment
contract.  The next computation should not re-extend this same cylinder.  It
should exploit the uniform `4/13` continuation on the formerly inert branch
in the amortized negative-mass route and test only the surviving multiplier-one
state `(26,-1)` for the next structurally distinct activation mechanism.  The
height-two state is closed by forced cofinal return.

## Factor twenty-seven is a source-rigid multiplier-one step

The only genuine negative factor-26 children have multiplier residue one,
height `26`, and centered error `-1`.  There are eight such children per
formerly inert parent, or `2056576060800` logical parents in total.  Generic
factor-27 algebra permits full and partial payments and both centered signs,
so the next probe must distinguish actual source support from that generic
mode list.

The exact checker starts from all eighteen digest-bound parent residues,
exhausts both possible factor-26 quotient parities, retains the four distinct
`C=1 mod 26` targets in each parity class, and evaluates every one of their
27 next source lifts.  The complete image is the double singleton

```text
C mod (26*27) = C mod 702 = 1,
D mod 27 = 1.
```

This is `3888=18*2*4*27` exhaustive source samples.  Restoring the factor-26
multiplicity and exact parent weights gives

```text
cofinal 0, positive 0, continuing negative 27
    : 2056576060800 parents,
payment 1, height 27, centered error -1
    : 55527553641600 refinements.
```

Thus factor 27 is not an activation mechanism: every actual refinement
continues the multiplier-one expanding boundary.  This is a complete mode
elimination, not evidence from a longer orbit horizon.

The singleton has a short analytic certificate.  Write the source-current
multiplier as `C=702z+1`.  The next divided multiplier is

```text
D = 473850z^2+648z+1
  = 27(17550z^2+24z)+1.
```

The Lean declarations `heightTwentySix_multiplierAtOneMod702Identity` and
`heightTwentySix_multiplierOneModTwentySeven` bind these identities.
`scripts/check_erdos243_t0_factor27_singleton.py` owns the exact parent census,
source-lift exhaustion, and source-digest experiment receipt.  Future work
must skip generic factor-27 modes and probe the next raw factor `28` on the
exact `(27,-1)` multiplier-one branch.

## Factor twenty-eight uniformly opens a positive-switch mode

The factor-27 singleton does not persist through the next raw factor.  The
complete checker exhausts

```text
18 parent residues * 2 quotient parities * 4 surviving factor-26 targets
  * 27 factor-27 lifts * 28 factor-28 lifts = 108864 source samples.
```

On those actual source lifts the successive exact multiplier images are

```text
C mod 19656 : 1, 5617, 8425
D mod 756   : 1, 109, 325
E mod 28    : 1, 21.
```

More importantly, every one of the `55527553641600` weighted factor-27
parents has the same child profile

```text
cofinal 0, positive 8, continuing negative 20.
```

Hence the negative continuation ratio is uniformly `20/28=5/7`; an
all-negative factor-28 parent does not exist.  In exact weighted counts,
`444220429132800` children switch positive and `1110551072832000` continue
negative.

The computation exposes a three-class analytic certificate.  Writing the
rigid factor-27 multiplier as `D=27q+1`, the next divided multiplier is

```text
E = 702q^2+25q+1,
q mod 28 in {0,4,12}.
```

Classes zero and twelve give `E=1 mod 28`, payment one, height twenty-eight,
and centered error `-1`.  Class four gives `E=21 mod 28`, payment seven,
height four, and centered error `+1`.  The Lean declarations
`heightTwentySeven_multiplierQuotientIdentity`,
`heightTwentySeven_quotientZeroMode`,
`heightTwentySeven_quotientFourMode`, and
`heightTwentySeven_quotientTwelveMode` bind the three residue identities.

`scripts/check_erdos243_t0_factor28_activation.py` owns the exhaustive census,
exact weighted profile, and source-digest experiment receipt.  The next
computation should restrict to the twenty multiplier-one negative children
and probe factor `29`; analytically, the new uniform `5/7` activation block
should be combined with the earlier effective `4/13` factor-26 block in the
amortized negative-mass or cumulative-LCM route.

## Factor twenty-nine uniformly kills the homogeneous boundary mode

The twenty multiplier-one negative children of every factor-28 parent split
again under the next raw factor.  The exact checker follows all

```text
18 * 2 * 4 * 27 * 20 = 77760 actual source parents
77760 * 29 = 2255040 source refinements.
```

Every source parent has the same quotient multiset modulo twenty-nine:

```text
q = 0^7, 15^8, 24^8, 25^4, 27^2.
```

Writing its height-twenty-eight multiplier as `E=28q+1`, the next divided
multiplier is

```text
F = 756q^2+26q+1.
```

The five actual quotient classes give the complete mode table

```text
q=0  : F=1  mod 29, payment 1,  height 29, error -1 : 7 children
q=15 : F=0  mod 29, payment 29, height 1,  error  0 : 8 children
q=24 : F=8  mod 29, payment 1,  height 29, error -6 : 8 children
q=25 : F=16 mod 29, payment 1,  height 29, error +5 : 4 children
q=27 : F=15 mod 29, payment 1,  height 29, error +7 : 2 children.
```

Consequently every one of the `1110551072832000` logical factor-28 parents
has profile

```text
cofinal 8, positive 6, continuing negative 15.
```

This eliminates the all-negative factor-29 fiber and kills the homogeneous
multiplier-one boundary mode with exact continuation `15/29`.  In weighted
counts there are `8884408582656000` full returns,
`6663306436992000` positive switches, and `16658266092480000` continuing
negative children.  The surviving negative support is no longer homogeneous:
seven children have state `(29,-1)` and eight have state `(29,-6)`, so the
next raw factors are respectively `30` and `35`.

The Lean declarations `heightTwentyEight_multiplierQuotientIdentity`, the
five `heightTwentyEight_quotient*Mode` identities, and
`heightTwentyEight_fullPaymentTwentyNine` bind the analytic certificate.
`scripts/check_erdos243_t0_factor29_activation.py` owns the complete source
census, exact logical weighting, source digests, and experiment contract.
The shared `centered_transport_next_multiplier_mod` primitive now reconstructs
the dynamically transporting next multiplier from any primitive centered
state, payment, and verified successor error.  This removes the negative-unit
assumption from future residue-cylinder continuations and is what the split
`-1` and `-6` branches need next.

For the formerly inert factor-25 branch, the exact continuation through the
factor-26, factor-28, and factor-29 activation blocks is now

```text
(4/13) * (5/7) * (15/29) = 300/2639.
```

This is an exact source-conditioned contraction, not yet a global transfer
theorem.  The next computation must stratify the two negative error modes
rather than extend a fictitious single multiplier-one cylinder.

## Factors thirty and thirty-five split rigidity from activation

The two negative factor-29 modes behave differently on their complete next
source cylinders.  The checker exhausts

```text
(77760 * 7) * 30 = 16329600 factor-30 refinements,
(77760 * 8) * 35 = 21772800 factor-35 refinements.
```

Every complete lift family is also compressed to an affine multiplier family
and then checked pointwise against all `30` or `35` lifts.  Thus the affine
rows are exact certificates, not extrapolations from two samples.

On the incoming state `(29,-1)`, all `544320` source families have the single
affine row

```text
G(lift) = 1 mod 30.
```

Every child therefore pays one and reaches `(30,-1)`.  Factor 30 is a
uniformly inert mechanism on the actual source, despite the positive and
partial-payment modes allowed by its generic residue table.
Writing the preceding factor-29 quotient as `q=29s`, the actual source uses
only `s=0,6 mod 30`, with refinement counts `10886400` and `5443200`.
Both lie in the generic root set on which the next multiplier equals one.

On `(29,-6)`, the `622080` source families split exactly:

```text
124416 = 1/5 : G(lift)=6 mod 35, profile (0 cofinal,0 positive,35 negative),
497664 = 4/5 : nonzero slope in {5,15,20,30},
                  image G={1,6,11,16,21,26,31} mod 35,
                  profile (0 cofinal,25 positive,10 negative).
```

The active image is the complete congruence class `G=1 mod 5`, each residue
occurring five times.  Residues `1,6` retain `(35,-6)`; residues `11,16,26,31`
switch positive with errors `9` or `4`; residue `21` pays seven and reaches
height five with error `+2`.  No actual factor-35 family contains a cofinal
child.  Averaging the exact source split gives negative continuation

Writing the preceding quotient as `q=29s+24`, the actual source uses fourteen
`s`-classes and excludes `s=1,8`, the two generic classes that would give full
payment `35`.  Thus the absence of a cofinal child is a source-image theorem,
not an omission from the generic mode table.  Averaging the exact source split
gives negative continuation

```text
(1/5)*1 + (4/5)*(10/35) = 3/7.
```

Consequently the factor-29 negative split followed by its appropriate raw
factor has continuation

```text
(7/29)*1 + (8/29)*(3/7) = 73/203.
```

For the formerly inert factor-25 branch, the now-certified activation chain is

```text
(4/13) * (5/7) * (73/203) = 1460/18473.
```

This decisively eliminates factor 30 as the next activation mechanism and
opens a source-stratified factor-35 contraction, but it does not close the
remaining inert support.  The next distinct cylinders are raw factor `31` on
`(30,-1)` and raw factor `41` on `(35,-6)`; the factor-35 slope-zero versus
nonzero source distinction must be retained.  The shared
`certify_complete_affine_lift_family` primitive now makes this pointwise
compression reusable by other residue-cylinder experiments.

## Corrected prime-field cascade: exact parent transport matters

The prime computation must first transport the height-29 multiplier through
factor `30` or `35` into the declared parent state.  Omitting that quotient
step classifies the wrong multiplier.  The corrected checker retains exact
division and then uses the unit source stride to transfer one complete field
table to every actual parent.

For `(30,-1)`, the corrected factor-31 image is

```text
0^4, 1^2, 6^2, 14^8, 21^2, 28^5, 29^8,
```

with universal profile `(4 cofinal,0 positive,27 negative)`.  The six negative
errors are `-1,-4,-5,-7,-9,-10`, with multiplicities `2,8,2,2,5,8` and raw
factors `32,35,36,38,40,41`.

For `(35,-6)`, the corrected factor-41 image is

```text
0^2, 9^13, 14^4, 15^4, 28^2, 30^6, 36^10,
```

with profile `(2 cofinal,39 positive,0 negative)`.  Factor `41` therefore
kills the entire negative factor-35 branch.  At this checkpoint the
factor-29 continuation is `189/899`, and the formerly inert factor-25 chain is
`540/11687`.

The multiplicity-eight `(31,-10)` mode has its own corrected factor-41 image

```text
0^8, 21^9, 24^4, 27^4, 30^6, 31^8, 37^2,
```

and profile `(8 cofinal,21 positive,12 negative)`.  Its negative children are
`(41,-20)` four times and `(41,-16)` eight times.  Processing this mode gives
factor-31 continuation `875/1271`, factor-29 continuation `6125/36859`, and
formerly inert factor-25 continuation `17500/479167`.

Finally, the corrected `(41,-20)` factor-61 image is

```text
0^4, 4^9, 18^10, 28^6, 31^14, 33^2, 43^10, 45^6,
```

with profile `(4 cofinal,6 positive,51 negative)`.  After resolving this
multiplicity-four child, the exact continuations are

```text
(31,-10) mode       : 692/2501,
factor-31 branch    : 53055/77531,
factor-29 cascade   : 371385/2248399,
factor-25 chain     : 1061100/29229187.
```

This is a genuine source-conditioned cofinal-return cascade, not a global
solution of #243.  The exact composite frontier is now
`32,35,36,38,40,57,64,66,75,76`.  It should be attacked with the reusable
exact composite transport pipeline rather than modular inverses across
nonunits.  The executable owners are
`scripts/check_erdos243_t0_factor31_41_field_activation.py`,
`scripts/check_erdos243_t0_factor41_error10_activation.py`, and
`scripts/check_erdos243_t0_factor61_error20_activation.py`.
