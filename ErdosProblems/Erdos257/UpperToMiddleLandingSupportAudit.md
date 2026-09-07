# Upper-to-middle landing support audit

## Purpose

This note records the laser pass on the remaining middle-reset sign problem.
It is a research reduction and exact computation record, not a proof of
Erdős 257.

Let an upper transition at source row `d` land at `s = d + 1`, and suppose
the transition from `s` is middle.  Write `R_s` for the integer seam
remainder, `Phi_s` for the exact floor error, and `S_s` for the selected
support.  The source-current identities give

```text
Z_s = R_s - Phi_s,             0 <= Phi_s < |S_s|.
```

Consequently the support bound

```text
|S_s| <= R_s
```

is sufficient for `Z_s > 0`, hence for positive middle-reset orientation.
The source-current floor-error estimates give a sharper sufficient integer
threshold.  If `m=|S_s|`, then

```text
Phi_s <= (4/7)m,
Phi_s < 2*floor(sqrt(2s))+4.
```

The first inequality sums `seamRankFloorError_le_four_sevenths`; the second
combines `seamWordFloorError_le_evenTruncationEnvelope` with
`evenTruncationFloorErrorEnvelope_lt_two_sqrt_add_four`.  Therefore it is
enough to prove

```text
M_s <= R_s,
M_s = min(floor(4m/7)+1, 2*floor(sqrt(2s))+4).       (SIGN)
```

This lowers the useful all-depth target from linear size to `O(sqrt(s))` on
large rows.  A failure of the sign is confined to the sharper window

```text
1 <= R_s <= Phi_s < M_s <= |S_s|.
```

This is the precise surviving target.  The base-four pullback and the
Möbius-centred carry congruence both reduce in this window to the cylinder
identity `C = -R_s (mod 4^L)`; they do not exclude it.

## Landed pulse cancellation

If `ell` is the largest false rank of the source row and remains strictly
late at the next row,

```text
2 * (d + 1) < 3 * ell,
```

then `ell` divides neither `2*d+1` nor `2*d+2`.  Therefore its boundary
pulse is zero.  Combining this with the existing late largest-false support
swap proves that the actual upper and lower adjacent words have identical
pulse.

The Lean declarations are:

- `rowPulse_eq_zero_of_nextLate_boundary` in
  `HalfCylinderBoundaryPulse.lean`;
- `seamAdjacentCut_abovePulse_eq_belowPulse_of_largestFalse_nextLate` in
  `HalfCylinderMiddleCarryLowerBound.lean`.

This removes the boundary-incidence defect exactly.  It does not bound the
signed previous-middle pullback coordinate, so it does not by itself prove
the sign or the parent endpoint.

## Exact scalar sharpness countermodel

Pulse cancellation cannot be combined with the late-gap and reset balance
alone to force a positive landing margin.  For any `m = d-ell >= 1` in the
next-late regime, set

```text
G = 2^(d+1) + (2*4^m + 4)/3,
P = 3,
O = 2^(d-1) - 1,
E = 4*O + P = 2^(d+1) - 1,
R = G - O,
R' = 1.
```

The division defining `G` is integral because `4^m = 1 (mod 3)`.  These
values satisfy all of the scalar identities used by the mature route:

```text
3G = 3*2^(d+1) + 2*4^m + 4,
R + O = G,
E <= 2^(d+1),
R' + E = 2^(d+1),
E + (4R - P - 4) = 4G - 4,
abovePulse = belowPulse = P.
```

They are also numerically compatible with an outgoing middle inequality at
the landing row.  Thus the complete scalar packet permits `R' = 1`.  This
is not an actual greedy-support counterexample; it proves that actual
support/divisor structure is indispensable and that no rearrangement of
the listed scalar equalities can prove even `R' >= 2`.

## Canonical-capacity anti-concentration is indispensable

There is also an exact greedy countermodel to any argument that retains the
Mersenne quotient weights, affine row scaling, mature support swap, pulse
cancellation, and upper-to-middle branch pattern but forgets the canonical
capacity `2^(2d-1)-2^d`.  It can be started one row earlier, at the
noncanonical row-five capacity

```text
C_5 = 565.
```

The exact row-five weights `[341,146,68]` give support `{2,3,4}` and
remainder `10`.  The affine update gives

```text
C_6 = 4*C_5 + 2^6 = 2324.
```

At row six the same support has remainder `101`; thus row five to six is a
middle step.  Its pulse is `3`, and the exact initial-middle excess is

```text
E = R_6-2^6 = 37 = 4*R_5-3.
```

In particular the preceding row already has the usual support-card buffer

```text
R_5 = 10 >= |S_5|+2 = 5.
```

Continue from the row-six capacity

```text
C_6 = 2324.
```

The exact row-six weights `[1365,585,273,132]` give support `{2,3,4}` and
remainder `101`.  Under the same affine capacity update,

```text
C_7 = 4*C_6 + 2^7 = 9424,
C_8 = 4*C_7 + 2^8 = 37952.
```

Exact greedy replay gives

```text
S_7 = {2,3,4,5},  R_7 = 3,
S_8 = S_7,         R_8 = 262.
```

Thus row six to seven is upper, row seven to eight is middle, the largest
false rank is `ell=5`, `2*(6+1)<3*ell`, and its boundary pulse is zero.
Nevertheless

```text
R_7 = 3 < 4 = |S_7|,
R_7 = 3 < 2^(6-5) * |S_7| = 8.
```

In the block coordinates below this is the case `h=1`, `m=4`, `P=1`,
`C_block=0`, for which

```text
R_7 = 4*37 - 2^7 - 4^2 - 1 = 3.
```

Thus even one exact preceding middle recurrence together with a preceding
support-cardinality gap does not prove the initial-excess threshold.  A
successful argument must use deeper canonical ancestry, not merely append
the known endpoint card bound one row earlier.

The checker replays this example bit for bit.  It proves that the remaining
argument must use the fixed canonical capacity, equivalently its global
dyadic ancestry; local greedy order and branch geometry are insufficient.

## Eight-generation affine-ancestry countermodel

The preceding obstruction is not confined to a one-row truncation.  Start at
row five from the deliberately noncanonical capacity

```text
C_5 = 370
```

and for every later row use the exact canonical affine update

```text
C_(s+1) = 4*C_s + 2^(s+1).
```

Run the same descending greedy algorithm with the exact Mersenne quotient
weights at every row.  Eight updates later the source row is `d=13`, with

```text
C_13 = 26337280,
C_14 = 105365504,
C_15 = 421494784.
```

The exact supports and remainders around the event are

```text
S_12 = {2,5,6,7,9,10},       R_12 = 1026,
S_13 = {2,5,6,7,9,10},       R_13 = 12293,
S_14 = {2,5,6,7,9,10,12},    R_14 = 0,
S_15 = S_14,                  R_15 = 32764.
```

Thus row `12 -> 13` is middle, row `13 -> 14` is upper, and row
`14 -> 15` is middle.  The upper event has

```text
(d,ell,h) = (13,12,1),
2*(d+1) < 3*ell,
A = S_13,
m = |A|+1 = 7,
C_block = 0,
P = 4.
```

Its initial middle excess is

```text
E = R_13 - 2^13 = 4101.
```

The exact thresholds are

```text
E-MID = 2^12 + 4 + ceil((4 + 2*7)/4) = 4105,
E-LIN = 2^12 + 4 + ceil((5*7 + 2)/3) = 4113.
```

Both fail, while the exact block identity still holds:

```text
R_14 = 4*4101 - 2^14 - 4^2 - 4 = 0.
```

This is a sharper local no-go than the row-six example: exact quotient
weights, greedy supports, the strict next-late geometry, and eight consecutive
affine capacity updates still do not force either initial-excess bound.  Its
scope is equally important.  The row-five capacity above is not the canonical
value `2^9-2^5=480`.  Therefore this is not a counterexample to the canonical
seam orbit and does not falsify E-MID there.  It retires only proofs that use a
bounded recent affine-ancestry window without also importing the distinguished
canonical origin, or equivalent information reaching beyond that window.

The exact checker function
`eight_generation_affine_ancestry_countermodel` replays every capacity,
support, branch, threshold, and block identity used above.

## Canonical-origin invariant and exact corridor

The affine recurrence has one exact conserved coordinate:

\[
 \beta_s=\frac{C_s}{4^s}+2^{-s},
 \qquad \beta_{s+1}=\beta_s.
\]

The canonical capacities `C_s=2^(2s-1)-2^s` are exactly the level
`beta=1/2`.  The eight-generation countermodel above lies instead on
`beta=201/512`, a permanent deficit of `55/512`.  Thus affine ancestry never
repairs a noncanonical origin; it merely transports its level exactly.

For any affine orbit and selected support `S` at row `s`, let

\[
 \Phi_s=\sum_{e\in S}
   \left\{\frac{4^s}{2^e-1}\right\}.
\]

Expanding the quotient floors gives the exact identity

\[
 R_s=4^s\left(\beta-
      \sum_{e\in S}\frac1{2^e-1}\right)-2^s+\Phi_s. \tag{COR}
\]

On the canonical level, put `M=2^h*m`.  The amplified-support failure
`R_s<M` is equivalent to the actual selected reciprocal sum entering

\[
 \frac12-2^{-s}-\frac{M-\Phi_s}{4^s}
 < \sum_{e\in S}\frac1{2^e-1}
 \le \frac12-2^{-s}+\frac{\Phi_s}{4^s}. \tag{AC}
\]

The upper inequality is just `R_s>=0`, and the corridor has exact width
`M/4^s`.  Consequently “use the canonical origin” now has a precise meaning:
prove an all-depth anti-concentration theorem excluding the actual greedy
support sum from (AC).  The invariant `beta=1/2` supplies the centre of this
corridor but no separation inside it.  Generic rational-denominator
separation is far too weak at the relevant least-common-multiple scale, and
same-block pulse charging cannot replace it because most selected ranks may
be pulse-silent.

The checker verifies conservation at both `beta=1/2` and `beta=201/512`, the
remainder identity (COR), the equivalence with (AC), and its exact width on
the bounded rows where the full `Fraction` diagnostic is enabled.  These are
exact identities and a reduction, not the missing anti-concentration theorem.

## Extended low-bit divisor-incidence window

There is a strictly stronger exact coordinate than any fixed small modulus.
For a landing row `s`, selected support `S`, and `t<=s`, expand each quotient
weight geometrically:

```text
W_s(e) = floor(2^(2s)/(2^e-1))
       = sum_(q*e<=2s) 2^(2s-q*e).
```

Let `L_t(S)` be the sum modulo `2^t` of precisely the displayed terms whose
exponent is below `t`.  Since the canonical capacity
`2^(2s-1)-2^s` is divisible by `2^s`, the landing remainder satisfies

```text
R_s == -L_t(S)  (mod 2^t).                           (LB)
```

Writing `c_S(n)=|{e in S:e divides n}|`, the same residue is

```text
L_t(S) == sum_(r=0)^(t-1) c_S(2s-r)*2^r  (mod 2^t).
```

Thus it is exactly the existing `finiteCoeffWindowNumerator` for the backward
window starting at `2s-t`, reduced modulo `2^t`; it is not a newly invented
unrelated register.  The advance is its exact connection to the canonical
landing remainder and target window.  The weighted-sum expansion itself is
already Lean-checked as `finiteCoeffWindowNumerator_eq_weighted_sum`; the new
landing congruence and the bounded certificate audit are ordinary exact
algebra/computation here, not a new Lean theorem.

For any positive target `M`, put `r_t=(-L_t(S)) mod 2^t`.  Then

```text
1 <= L_t(S) <= 2^t-M    iff    r_t >= M.
```

Because `R_s` is nonnegative and congruent to `r_t`, either condition is an
exact certificate that `R_s>=M`.  Taking
`M=2^(d-ell)|S_s|` therefore turns the amplified landing target into a
finite low-binary divisor-incidence window.  Unlike the two-bit pulse, this
window is allowed to widen with the target.

Exact replay through source row `5000` certifies every one of the `584`
strict next-late events.  Starting at the natural scale
`t_0=ceil(log_2 M)`, the first certificate occurs at `t_0+j` with

```text
j : event count
0 : 169
1 : 184
2 : 107
3 : 59
4 : 32
5 : 13
6 : 11
7 : 6
8 : 3
```

The first maximum eight-extra-bit event in this range is

```text
(d,ell,h,s,M,t) = (1656,1655,1,1657,1622,19),
L_t = 261417,  (-L_t mod 2^t) = 262871.
```

For the direct-card target `M=|S_s|`, the same exact replay also
certifies all `584` strict events.  Its extra-bit histogram is

```text
j : event count
0 : 166
1 : 202
2 : 91
3 : 63
4 : 29
5 : 13
6 : 7
7 : 5
8 : 5
9 : 3
```

The maximum is therefore nine extra bits in this window (first at `d=62`,
`ell=60`, `|S_s|=31`).  This direct-card statistic is closer to the sign
problem than the amplified target, but it is likewise bounded evidence only.

The source-current sign target `(SIGN)` is smaller.  Its low-bit audit uses

```text
M_s = min(floor(4|S_s|/7)+1, 2*floor(sqrt(2s))+4).
```

This threshold is rigorously sufficient by the cited Lean floor-error bounds;
only the subsequent all-depth low-bit clearance remains computational here.
Through source row `5000`, all `584` strict events clear this sharper target.
The extra-bit histogram is

```text
j : event count
0 : 172
1 : 219
2 : 89
3 : 52
4 : 28
5 : 7
6 : 9
7 : 6
8 : 1
12: 1
```

The unique maximum is

```text
(d,ell,s,m,M_s) = (4266,4265,4267,2139,188),
base width = 8, first certificate width = 20,
(-L_20 mod 2^20) = 524454.
```

Thus the square-root target is a real reduction in the required remainder,
but it does not make the additive width overhead monotonically smaller.

The natural-width statement `t=t_0` is false already at source `d=41`:
there `M=60`, `t_0=6`, and the negative residue is only `6`.  Thus this does
not revive a fixed-modulus argument.  The new proof target is a
uniform (or otherwise controlled) extended-window theorem forced by the
ordered canonical ancestry.  The computation proves neither a uniform `+8`
bound nor the all-depth landing inequality.

There is an exact interpretation of the extra width which is useful for
future attacks.  Put `b=ceil(log2 M)` and `u=R_s mod 2^b`.  If `u>=M`, the
base window certifies.  Otherwise write

```text
floor(R_s/2^b) = 2^z * odd.
```

Then every width through `b+z` still has residue `u<M`, while width
`b+z+1` has acquired the next binary one and certifies.  Hence

```text
extra width = 1 + the zero-run length immediately above bit b of R_s.
```

The controlled-width problem is therefore exactly a canonical remainder
zero-run problem, not a generic accumulation estimate for `L_t`.

### Exact carried-incidence plateau reduction

The zero run has an equally exact formulation on the divisor-incidence side.
Let `L=L_s(S_s)` be the full backward incidence numerator and write

```text
L = A + 2^b H,                 0 <= A < 2^b,
b = ceil(log2 M_s).
```

The full-window congruence and `0<R_s<2^s` give

```text
R_s = (-L mod 2^s).
```

If the base window fails, put `u=R_s mod 2^b<M_s`.  Then

```text
A > 0:  u = 2^b-A,
         floor(R_s/2^b) = (-H-1 mod 2^(s-b));
A = 0:  u = 0,
         floor(R_s/2^b) = (-H mod 2^(s-b)).
```

Consequently the zero run `z` immediately above bit `b` is exactly

```text
z = v_2(H+1)    when A>0,
z = v_2(H)      when A=0.
```

Equivalently, the carried binary incidence digits beginning at bit `b` are
`1^z 0` in the first case and `0^z 1` in the second.  More decisively, once
the base window has failed, failure of the sufficient target `(SIGN)`, namely
`R_s<M_s`, is equivalent to

```text
2^(s-b) divides H+1    when A>0,
2^(s-b) divides H      when A=0.                 (PLATEAU-SIGN)
```

Thus the missing sufficient sign theorem is a canonical two-adic anti-concentration
statement for one carried divisor-incidence integer.  For example, after a
finite small-row check, either of the following would suffice:

```text
v_2(H+1) <= 2b or v_2(H) <= 2b, as applicable;
more strongly, z+1 <= 2b, hence a certificate by width 3b.
```

The exact replay checks the stronger candidate `z+1<=2b` on all `12547`
strict canonical events through source row `100000`, with no failure.  The
largest observed run is `z=13`, at

```text
(d,ell,s,M_s,b) = (88621,88620,88622,846,10).
```

There the carried digits from bit `b` are thirteen ones followed by a zero.
This is finite evidence, not an all-depth valuation bound.

At an actual incoming upper reset this reformulation collapses exactly to the
existing charge ceiling.  Put `d=s-1` and let `E_d` be the reset charge.  The
Lean theorem `seamUpperBranch_remainder_add_resetCharge_eq` gives

```text
R_s + E_d = 2^s.
```

Since the full incidence swap gives `L = Q*2^s+E_d`, write
`E_d=a+2^b e`, `0<=a<2^b`.  Then `A=a` and

```text
H = Q*2^(s-b)+e.
```

If `A=0`, positivity gives `1<=e<2^(s-b)`, so the `A=0` divisibility in
`(PLATEAU-SIGN)` is impossible.  If `A>0`, then

```text
2^(s-b) divides H+1
  iff e+1 = 2^(s-b)
  iff E_d = 2^s-2^b+A
  iff R_s = 2^b-A.
```

Under base-window failure, `2^b-A` is exactly the failed residue.  Therefore
the dangerous plateau condition is not a new capacity-derived invariant:

```text
PLATEAU-SIGN  iff  R_s < M_s
              iff  E_d + M_s > 2^s.
```

Equivalently, proving `(SIGN)` here is precisely the target-specific upper
reset charge ceiling `E_d+M_s<=2^s`.  This is the `T=4M_s` instance of
`seamUpperReset_landingScale_iff_chargeCeiling`, and it is weaker than either
`SeamUpperResetChargeCeilingProducer` or the `j=0` conclusion of
`SeamUpperResetDyadicBandEscape`.  The valuation coordinate is still useful
for computation, but it does not evade the source-current producer.

The canonical origin is essential.  Start instead at row five with exact
capacity `C_5=506`, whose normalized seed is

```text
(C_5+2^5)/2^10 = 269/512
```

rather than the canonical `1/2`, and then use the same affine capacity update
and exact descending greedy rule.  Eight updates later, row `13 -> 14` is
upper with largest false rank `10`, row `14 -> 15` is middle, and

```text
|S_14|=5,  M_14=3,  b=2,  R_14=8193=2^13+1.
```

The first successful width is `14`, so the extra width is `12>2b`.  This is
an exact noncanonical falsifier: the affine recurrence and local
upper-to-middle geometry alone do not imply the proposed plateau bound.  A
proof must use the distinguished canonical `1/2` ancestry, not merely a
bounded recent orbit segment.

The existing Boolean-prefix valuation lemmas do not supply that use of the
ancestry.  Both
`binaryCoeffPrefixNumerator_terminal_zero_of_pow_two_dvd` and its `+1`
companion assume coefficients at most one, and only under that hypothesis
turn a large valuation into a terminal empty or full support block.  Here the
digits of `L` are the divisor multiplicities `supportCoeff`, not membership
bits; at the canonical row-`4266` record they begin

```text
19, 3, 1, 2, 1, 0, 17, 1, 1, 5, 2, 2, ...
```

The obstruction is already visible in two digits.  Under the recursion
`B_(j+1)=2B_j+c_(j+1)`, coefficients `(1,2)` give numerator `4`, divisible
by four, although the terminal coefficient is not zero; `(0,3)` gives
numerator `3`, so numerator plus one is divisible by four although the
terminal coefficient is not one.  Thus the Boolean proof cannot be
transferred to the carried incidence integer.  The centred recurrence has
signed forcing `supportCoeff-1`, so cancellation, rather than a literal
support gap, can create the valuation.

There is also an exact finite-anchor no-go.  Freeze any finite support pattern
on ranks at most `N` and impose the corresponding residue class for `s` modulo
`lcm(2,...,N)`.  For a desired carried word of length `T`, choose distinct
fresh primes `p_r>max(N,T)` and, whenever a fresh support bit is used, impose
`2s=r (mod p_r)`.  Such a prime contributes to exactly the `r`-th incidence
coefficient in this window.  Choosing the fresh bit recursively against the
known coefficient and incoming carry programs every desired carried word;
CRT realizes all the congruences simultaneously.

For example, freeze the actual row-`4267` support through rank `512`.  It has
`235` selected anchors.  Adding the abstract fresh incidences at positions

```text
2,4,6,7,8,9,10,11,14,15,16,17,18,20,23
```

gives `m=250`, `M=143`, `b=8`, coefficient word

```text
4,3,8,1,2,1,6,1,15,3,2,2,1,0,11,2,2,5,2,1,10,0,9,2,5
```

and carried word

```text
0,1,0,0,1,1,1,0, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, 0.
```

Thus `L mod 256=114`, so `-L mod 256=142=M-1`, followed by sixteen
zero bits in `-L`; the first certificate would have `extra=17>2b=16`.
Fresh primes can be taken large enough to make their reciprocal mass
arbitrarily small.  This construction does **not** assert that the resulting
abstract support is the canonical descending-greedy support at its CRT row.
It proves the exact narrower no-go: no argument from a fixed canonical anchor
prefix, Boolean Mobius inversion, parity, and capacity positivity alone can
establish the `2b` bound.  A proof must use the unbounded descending-greedy
ancestry (or an equivalent global selection inequality).

### A failed `(SIGN)` target forces a near-full-shell right return

There is one further exact consequence on the dynamical side.  Suppose
`s>=12` is a middle row, `R_s<M_s<=2^b`, the next `k` transitions obey the
right recurrence, and the following transition carries.  The Lean theorem
`middleResetDeviation_eq` gives

```text
dev_s = 4R_s-p_s < 4M_s <= 2^(b+2),
```

while `rightRun_scaledDeviation_gt_of_terminalCarry` gives

```text
2^(s+k) < 4^k dev_s.
```

Comparison of powers of two therefore forces

```text
k >= s-b-1.                                      (RETURN-DELAY)
```

This implication is Lean-checked as
`rightRun_length_ge_of_middle_small_of_terminalCarry` in
`HalfCylinderPullbackCardPropagation.lean`.

So a target-failing landing cannot quickly return through a right block: any eventual
carry lies within `b+1` rows of the full shell.  This is a genuine canonical
consequence of a hypothetical sign failure, but it does not yet contradict
the corpus.  Together with `middlePrev_forces_not_middleInequality`, it forces
the transition immediately after the bad middle landing to be right.  More
generally, the first non-right transition before time `s-b-1`, if there is
one, must itself be middle.  The available right-run length bound starts from
an upper row; no source-current theorem upper-bounds a right run originating
at this middle row, and that intervening middle remains the escape hatch.

The long return also falls just outside the existing late-largest-skip socket.
Put `t=s+k+1`.  If `2b<=s`, `(RETURN-DELAY)` gives

```text
t >= 2s-b,
2t >= 4s-2b >= 3s.
```

But both `LargestSkipLateStepSocket` and
`three_mul_largestSkipLowerWeight_add_exactLateGap_eq_upperWeight` require the
strict opposite inequality `2t<3s`.  The selected suffix preserves largest
false rank `s`, but the delay has moved the endpoint from the quotient-two
late-gap regime into the quotient-three/four regime.  Thus those consumers
cannot be composed with `(RETURN-DELAY)` by a sign flip.

The full-shell bridge does not repair this mismatch by itself.  If
`s+1,...,t-1` are selected and `t<=2s` is the first later skip, then its
contribution at horizon `2s` is only

```text
2^(2s-t) <= 2^b,
```

and even declaring every later rank skipped gives total future-skip capacity
at most `2^(b+1)-1`.  This is an upper bound, whereas
`futureSkipCapacity_factorization` needs a coverage lower bound plus actual
half-greedy alignment.

An exact noncanonical orbit proves that the local hypotheses are jointly
consistent.  At row `11`, start from capacity `1805057`; exact quotient greedy
has support `{2,4,6,7,8,9}` and remainder `3078`.  Then

```text
11 -> 12  upper at 10, R_12=4<M_12=5<=2^3;
12 -> 13  middle;
13,...,21 nine consecutive right sources;
22 -> 23  upper at largest false rank 12;
23 -> 24  middle.
```

Here `k=9>=12-3-1`, the terminal upper still occurs before the full shell
(`22<24`), yet `2*22=44>=3*12=36`.  This does not falsify canonical `(SIGN)`.
It retires the attempted composition using only local return timing, the
late-gap socket, and unaligned full-shell capacity.  A surviving proof needs a
canonical non-late gap estimate or an actual frozen-margin coverage/alignment
theorem.

### Full-window collapse to the terminal centred carry

The window is not an independent random register.  The existing Lean theorem
`finiteCoeffWindowNumerator_sub_baseline_eq_centeredCarry` gives, for every
`t<=s`,

```text
L_t(S) - (2^t-1)
  = 2^t*e_S(2s-t-1) - e_S(2s-1),
```

where `e_S` is `mobiusCenteredHalfCarry`.  Therefore

```text
R_s == 1 + e_S(2s-1)  (mod 2^t).
```

At the full window, combining this telescope with
`frozenMargin_fullShell_eq_stemTruncatedSum_sub_target` gives the exact
integer identity

```text
e_S(2s-1) + 1 = 2^s + R_s.                         (TC)
```

For the mature upper landings in this audit, the already proved reset balance
has `R_s<2^s`.  Hence the full-width residue is literally `R_s`, not merely a
congruent lower bound.  Consequently the unconstrained assertion

```text
there exists t<=s with (-L_t mod 2^t) >= |S|
```

does not advance the proof: at `t=s` it is exactly the desired inequality
`R_s>=|S|`.  A useful window theorem must control the width before the full
shell, for example by `ceil(log2 |S|)+O(1)`, and that control must use actual
canonical ancestry.  This is an exact reduction from two Lean-checked
identities; it is not a new parent theorem.

### Arbitrary finite-window CRT obstruction

There is an exact obstruction to proving such controlled width from the local
landing shape alone.  For every `t>=1` one can construct a support having all
of the following properties:

```text
{2,3} subset S,              {4,5} disjoint from S,
c_S(2s-r) <= 3               (0 <= r < t),
L_t(S) == 0                  (mod 2^t),
```

while also embedding it into a strict next-late upper-to-middle-shaped triple
of support words.

Here is the construction.  Fix the residue class of `s` modulo six and put

```text
b_r = 1_(2 divides 2s-r) + 1_(3 divides 2s-r),
q_0 = 0.
```

Inductively choose `x_r in {0,1}` with

```text
x_r == b_r+q_r (mod 2),
q_(r+1) = (b_r+x_r+q_r)/2.
```

Then `0<=q_r<=2`, and telescoping the binary carry gives

```text
sum_(r<t) (b_r+x_r)2^r = q_t 2^t.                 (CRT-CARRY)
```

For every `r` with `x_r=1`, choose a distinct prime `p_r>max(t,5)` and impose
`2s==r (mod p_r)`.  The Chinese remainder theorem realizes all these
conditions together with the chosen class modulo six.  Taking a sufficiently
large representative ensures every `p_r<s-1-t` and `s>3t+3`.  Because
`p_r>t`, it divides exactly one integer in the window
`2s,2s-1,...,2s-t+1`.  Thus the support

```text
A = {2,3} union {p_r : x_r=1}
```

realizes `c_A(2s-r)=b_r+x_r<=3`, and `(CRT-CARRY)` gives zero residue.
Put `d=s-1`, `ell=s-1-t`, and use the three symbolic support words

```text
S_d     = A union {ell+1,...,d-1},
S_(d+1) = A union {ell},
S_(d+2) = S_(d+1).
```

They have the exact upper-then-middle word change, `ell` is the largest false
source rank, and `2(d+1)<3ell`.  The added `ell` does not divide any of the
first `t` backward-window rows, so it does not change the zero residue.

The checker replays the recurrence, CRT realization, coefficient ceiling,
zero residue, and strict landing geometry for every width through `128` and
all six residue classes of `s` modulo six.  The algebra proves the construction
for every finite `t`; the bounded replay is only an implementation audit.

This does **not** falsify the canonical landing inequality: the constructed
words are not asserted to be reachable from the canonical capacity.  It proves
that forced small ranks, omitted ranks `4,5`, strict suffix geometry, and even
a uniform divisor-coefficient ceiling cannot yield controlled low-bit
clearance.  Any successful low-bit theorem must use the complete canonical
greedy ancestry, not merely a longer local divisor window.

There is also a sharp algebraic boundary behind this window.  With the block
notation below, largest-false gap plus upper carry gives only

```text
4*(D-C_h) >= P,
```

which is exactly `R_(d+1)>=0`.  If one uses only the crude bound
`Phi<m`, the direct-card reserve is

```text
4*(D-C_h) >= P+m    iff    R_(d+1) >= m=|S_(d+1)|.
```

This direct cardinal reserve already yields positive real orientation because
the floor error is strictly below `m`.  The stronger amplified route replaces
`m` by `2^h*m`.  The sharper source-current reserve instead replaces `m` by
`M_s` from `(SIGN)`.  No rearrangement of the existing scalar gap/carry
identities supplies any positive reserve beyond `R>=0`; the extended low-bit
window retains genuinely additional divisor-incidence information.

## Exact canonical surplus coordinate

For a mature canonical event put `h=d-ell` and

```text
W_d(e) = floor(4^d/(2^e-1)).
```

In the late range `d>3h`, exact division gives

```text
W_d(d-k) = 2^(d+k) + 4^k                 (1 <= k <= h),
W_d(ell) - sum_{j=ell+1}^{d-1} W_d(j)
  = 2^(d+1) + C_h,
C_h = (2*4^h+4)/3.
```

Let `D=R_d-3*2^(d-1)` and let `P` be the actual pulse of the common landing
prefix.  The exact suffix swap and pulse cancellation then reduce the landing
remainder to

```text
R_(d+1) = 4*(D-C_h) - P.
```

Consequently the amplified support target is exactly equivalent to

```text
D-C_h >= ceil((P + 2^h*|S_(d+1)|)/4).
```

This is not a proof of the inequality.  It is the smallest surviving
canonical producer: all floor and denominator terms have disappeared, while
the load-bearing ordered selected-prefix pulse register remains.

## Same-largest-false block collapse

There is a further exact cancellation in the strictly next-late case.  Put

```text
A = S_(ell+1),
m = |A|+1 = |S_(d+1)|,
E = R_(ell+1)-2^(ell+1).
```

The late support pullback and the full-suffix right-branch theorem give

```text
S_j = A union {ell+1,...,j-1}       (ell+1 <= j <= d),
S_(d+1) = A union {ell}.
```

For `ell+1 <= j <= d-1`, let

```text
p_j = sum_(e in S_j) rowPulse(j,e),
C_block = sum_(j=ell+1)^(d-1) 4^(d-1-j)*p_j,
P = sum_(e in A) rowPulse(d,e).
```

The last formula for `P` uses strict next-lateness twice: the filled suffix
is pulse-invisible and the boundary rank `ell` has zero pulse.  Every step
before the upper landing is an actual right step, so

```text
R_(j+1) = 4*R_j - 2^(j+1) - p_j - 4.
```

Unrolling these `h-1` recurrences and substituting

```text
C_h = (2*4^h+4)/3
```

into the canonical surplus identity gives

```text
D-C_h = 4^(h-1)*E - 2^(d-1) - 4^h - C_block.
```

Therefore the landing remainder has the exact block form

```text
R_(d+1)
  = 4^h*E - 2^(d+1) - 4^(h+1) - 4*C_block - P.       (BLOCK)
```

Since strict next-lateness implies `ell>2h+2`, all exponents below are
ordinary nonnegative exponents.  The amplified support target is thus
equivalent to the single initial-middle-excess threshold

```text
E >= 2^(ell-h+1) + 4
       + ceil((4*C_block + P + 2^h*m)/4^h).           (E-MID)
```

This removes the final floor arithmetic and locates the missing information
one block earlier: it is a lower gap above the dyadic staircase
`2^(ell-h+1)`, in the actual middle remainder `R_(ell+1)`.

There is also a coarse pulse-free sufficient form.  For every support rank
`e>=2`, `rowPulse(j,e)<=2`, since `e` cannot divide both consecutive
integers `2j+1` and `2j+2`.  Hence

```text
C_block < (2/3)*(m+h)*4^(h-1),
P <= 2*(m-1).
```

It follows from `(E-MID)` that the stronger linear buffer

```text
E >= 2^(ell-h+1) + 4 + ceil((5*m+2*h)/3)             (E-LIN)
```

is sufficient.  Thus the ordered pulse packet is geometrically damped after
the exact pullback.  What remains load-bearing is global canonical ancestry
strong enough to prove `(E-MID)`, or even the stronger `(E-LIN)`; neither
inequality is proved here.

## Pulse-silent obstruction to direct charging

The same block calculation also falsifies a natural injective proof plan.
A selected prefix rank can be pulse-silent throughout the whole block.  For
such a rank `e`, every quotient weight scales exactly as

```text
W_(j+1)(e) = 4*W_j(e),
```

so it contributes nothing to `C_block` or `P`, while it still contributes
one unit to `m`.

The exact canonical replay through source row 5,000 contains an extreme
instance at

```text
(d, ell, h) = (4971, 4970, 1).
```

Here `A` has cardinality `2496`, but only eleven ranks of `A` have nonzero
pulse at either row in the block `j in [ell,d]`; the other `2485` selected
ranks are pulse-silent.  The total prefix pulse over those two rows is `13`,
with `P=8` and `C_block=0`, whereas `m=2497`.  Consequently no injection from
selected prefix ranks to same-block pulse occurrences can supply the support
term in `(E-MID)`.  Silent ranks must be paid by the initial excess `E`, or by
an equivalent global-ancestry coordinate.

The algebraic identity `(BLOCK)` is exact, and the silent-rank count is an
exact finite canonical computation.  They are respectively a reduction and
a no-go result, not a proof of the all-depth producer or of Erdős 257.

## Exact computation

Run:

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/upper_to_middle_landing_support_audit.py 5000 200
```

The replay uses exact integers and `Fraction` values only.  Through source
row 5,000 it finds 585 upper-to-middle events and no failure of

```text
2^(d-ell) * |S_(d+1)| <= R_(d+1).
```

Including the finite base event, the minimum slack is

```text
(d, ell, R_(d+1), |S_(d+1)|) = (13, 7, 392, 4),
slack = 392 - 2^6 * 4 = 136.
```

Every later audited event satisfies `2*(d+1) < 3*ell` and has zero boundary
pulse.  Landing remainders occupy every residue class modulo
`2, 3, 4, 5, 7, 8, 16`, so no fixed congruence separates the dangerous
window.

On the `584` strictly next-late events through source row `5000`, exact
replay also checks `(BLOCK)` and `(E-MID)` directly, with no identity failure
and no threshold failure.  The row-`13` finite base event is not strictly
next-late and is therefore outside this block statement.

A falsifier for the amplified candidate would be an actual upper-to-middle
event with

```text
E_d > 2^(d+1) - 2^(d-ell) * |S_(d+1)|,
```

where `E_d = 2^(d+1) - R_(d+1)` is the upper reset charge.
No such event occurs in the audited range.

For a larger low-bit-only replay, run the exact adjacent-row engine:

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/extended_low_bit_window_probe.py 100000 --validate 500 --incidence-plateau --anchor-programming
```

It checks the fast recurrence against direct greedy construction through row
`500`, reproduces every published row-`5000` count and extremum, and then
continues exactly through row `100000`.  There are `12547` strict events and no
failure of the direct-card, amplified, or hybrid sign target.  The additive
width records do grow:

```text
target          max extra bits       first record (d,ell)
direct card          14              (15138,15137)
amplified            18              (31850,31845)
hybrid sign          14              (88621,88620)
```

The checkpoint maxima `(direct, amplified, hybrid)` are

```text
row 5000 : ( 9,  8, 12)
row 10000: ( 9,  9, 12)
row 20000: (14, 13, 12)
row 50000: (14, 18, 12)
row 100000: (14, 18, 14)
```

This falsifies the observed `+8` and `+9` constants as universal guesses; it
does not falsify the existence of some larger uniform constant.  Together
with the exact zero-run law, the data instead points toward controlling the
record length of binary zero blocks in canonical landing remainders.  Any
asymptotic claim remains conjectural.

## Rank-only intermediate producer

There is a cleaner sufficient target between the canonical ancestry and the
support-sensitive pullback-card inequality.  In the late-upper/right-run
coordinates of `HalfCylinderPullbackCardPropagation.md`, let `s` be the upper
source, `k` the realized right length, and `Q_k` the exact preceding-middle
pullback coordinate.  The endpoint support lies in

```text
{2,...,s+k},
```

so it has cardinality at most `s+k-1`.  Consequently the rank-only bound

```text
Q_k >= s+k+1                                      (Q-RANK)
```

immediately gives

```text
|S_(s+k+1)|+2 <= s+k+1 <= Q_k,
```

which is the pullback-card premise `(PC)` consumed by the existing two-block
propagation theorem.  This reduction does not attempt to charge individual
support ranks, so the pulse-silent obstruction above does not apply to the
implication itself.

The exact canonical forced-seam replay through row `2500` has no failure of
`(Q-RANK)`.  Its minimum slack is

```text
Q_k-(s+k+1) = 4
```

at `(s,d,k)=(19,14,1)`, where `Q_k=25` and the endpoint row is `21`.  This is
bounded exact evidence only.  The all-depth rank inequality is not proved,
and neither the pullback-card producer, the canonical E-MID inequality, half
membership, nor Erdős 257 follows from the computation alone.

## What remains

After pulse cancellation, the amplified candidate rewrites into a lower
bound on the signed previous-middle staircase/pullback coordinate.  At zero
right-run length this is stronger than the existing open critical-gap
cardinality producer.  The current corpus supplies the exact pullback
identity and propagates a pullback-card margin once assumed, but it does not
produce that margin.

Thus this pass retires fixed-modulus and scalar-only attacks.  The remaining
proof route is genuinely ancestry-sensitive: prove the sharper
`M_s <= R_s` at actual upper-to-middle landings, prove a controlled-width
low-bit certificate for that target using canonical reachability, or prove the
stronger staircase-amplified inequality above.  None of these all-depth
statements is claimed proved here.
