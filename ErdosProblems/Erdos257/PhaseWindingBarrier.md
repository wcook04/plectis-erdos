# Phase winding and the protective-alternate barrier

Status: exact deductions and exact finite computation, 2026-08-20.  The
phase-winding inequality in Section 4 is conjectural.  It has been checked
only on the finite range stated there.

## 1. The divisor clock is an integer winding of one circle map

Retain the notation of `FirstFailureGreedyBridge.md`.  Thus

\[
 \alpha_m=\left\{\frac{2^m}{21}\right\},\qquad
 \Phi_m=\sum_{d<m}b_d\frac{2^{m\bmod d}}{2^d-1},
 \qquad
 Y_m=C_m+\alpha_m-\Phi_m.
 \tag{1}
\]

Put

\[
 \vartheta_m=\{\Phi_m-\alpha_m\},\qquad
 K_m=C_m-\lfloor\Phi_m-\alpha_m\rfloor.
 \tag{2}
\]

Then

\[
 \boxed{Y_m=K_m-\vartheta_m.}                         \tag{3}
\]

The separate source and divisor recurrences give

\[
 \alpha_{m+1}=2\alpha_m-t_{m+1},
 \qquad
 \Phi_{m+1}=2\Phi_m+\frac{2b_m}{2^m-1}-h(m+1).
\]

Both `t_(m+1)` and `h(m+1)` are integers.  Consequently

\[
 \boxed{
 \vartheta_{m+1}
 =\left\{2\vartheta_m+\frac{2b_m}{2^m-1}\right\}.}
 \tag{4}
\]

Thus the divisor pulses are not additional fractional forcing.  They are
the integer winding numbers discarded when the phase is reduced modulo one.
The period-six source has the same status.  The fractional dynamics is one
perturbed doubling map; the quotient defect records its integer sheet.

This gives an exact angular form of the seam.  Write

\[
 L_{m,k}=2^m\sum_{j=1}^k\frac1{2^{m+j}-1},qquad
 U_m=\frac{2^m}{2^m-1},qquad
 \delta_{m,k}=1-L_{m,k}.
\]

Since `L_(m,k)<1<U_m<2`, the interval

\[
 L_{m,k}\leq Y_m<U_m                                  \tag{5}
\]

has two angular sheets:

\[
 \begin{array}{ll}
 K_m=1:&0\leq\vartheta_m\leq\delta_{m,k},\\[2mm]
 K_m=2:&1-\dfrac1{2^m-1}<\vartheta_m<1.
 \end{array}                                           \tag{6}
\]

The second line is the narrow upper sliver in which `1<=Y_m<U_m`.  Every
actual `0 1^k` seam start through rank `10000` lies on the first sheet; this
is finite evidence, not an exclusion of the upper sliver.

## 2. Force the protective digit and freeze the suffix

Suppose the actual greedy decision at rank `m` is a rejection.  Define the
protective alternate `a^(m)` by

\[
 a^{(m)}_d=b_d\quad(d<m),\qquad
 a^{(m)}_m=1,\qquad
 a^{(m)}_d=0\quad(d>m).                               \tag{7}
\]

This finite sum exceeds `1/21`.  Its scaled excess at the forcing rank is

\[
 \Delta_m
 =\frac{2^m}{2^m-1}-Y_m>0.                           \tag{8}
\]

Let `q_n^(m)`, `P_n^(m)`, `F_n^(m)` and `Phi_n^(m)` denote the quotient,
count, endpoint-compensated, and fractional states of (7).  At rank `m`,

\[
 \Phi_m^{(m)}-\alpha_m=q_m^{(m)}+\Delta_m.             \tag{9}
\]

There are no later selected digits in (7), so (4) becomes the unperturbed
doubling map after rank `m`.  More precisely, for every `k>=0`,

\[
 \boxed{
 \Phi_{m+k}^{(m)}-\alpha_{m+k}
 =q_{m+k}^{(m)}+2^k\Delta_m.}                         \tag{10}
\]

The fractional part is therefore `{2^k Delta_m}`.  Every divisor pulse in
the zero continuation contributes only to the integer `q_(m+k)^(m)`.  This
is the promised renormalisation of the joint suffix/LCM phenomenon: binary
suffix capacity is the doubling of `Delta_m`, while the LCM pulses are the
winding number of the same orbit.

## 3. The divisor pulses telescope out of the energy change

For `n>m`, let `p_n^(m)` be the proper-divisor load of the word (7), and put

\[
 s_n^{(m)}={\bf1}_{2\mid n}a^{(m)}_{n/2}.
\]

Since the terminal bit is zero, the defect and `F` recurrences are

\[
 q_n^{(m)}=2q_{n-1}^{(m)}+t_n-p_n^{(m)},
 \qquad
 F_n^{(m)}-F_{n-1}^{(m)}=p_n^{(m)}+s_n^{(m)}-q_n^{(m)}.
\]

Eliminating `p_n^(m)` and summing gives the exact endpoint identity

\[
 \boxed{
 F_{m+k}^{(m)}
 =F_m^{(m)}+2\bigl(q_m^{(m)}-q_{m+k}^{(m)}\bigr)
  +\sum_{j=1}^k\bigl(t_{m+j}+s_{m+j}^{(m)}\bigr).}
 \tag{11}
\]

No internal divisor count remains in (11).  A large LCM pulse can lower the
endpoint defect only by contributing the corresponding amount to the
`F`-increment.  The only uncancelled data are the two endpoint defects, the
period-six source count, and the half-scale crossings.  This is an exact
form of the compensation which was obscured in the raw borrow recurrence.

Now assume `1<=k<m`.  At horizon `N=m+k`, all ranks in the words

```text
1 0^k    and    0 1^k
```

lie above `N/2`.  The superincreasing `F` coefficients therefore give

\[
 F_N(1 0^k)-F_N(0 1^k)=k+1.                          \tag{12}
\]

Hence a seam (5) can cause a negative value of `F_N` only if

\[
 F_{m+k}^{(m)}\leq k.                                 \tag{13}
\]

Equation (13) is the transient overshoot that must be excluded.  The
protective word is genuinely infeasible, so its defect eventually tends to
minus infinity and its `F`-value eventually tends to plus infinity.  The
issue is whether its integer quotient orbit can cross (13) before that
eventual growth takes over.

## 4. A phase-winding height which excludes the overshoot

Define the integer potential

\[
 \begin{split}
 \mathcal H_{m,k}
 &:=F_{m+k}^{(m)}-k-\left\lceil2^k\Delta_m\right\rceil\\
 &=P_{m+k}^{(m)}+4-k-q_{m+k}^{(m)}
   -\left\lceil\Phi_{m+k}^{(m)}-\alpha_{m+k}\right\rceil.
 \end{split}                                          \tag{14}
\]

The equality follows from (10).  This potential Booleanises the fractional
phase by its integer winding ceiling.  It retains both quantities that the
earlier separate approaches lost: the dyadically amplified real excess and
the endpoint quotient margin.

There is an exact one-step recurrence.  Put

\[
 c_k=\left\lceil2^k\Delta_m\right\rceil,\qquad
 W_{m+k}=q_{m+k}^{(m)}+c_k
 =\left\lceil\Phi_{m+k}^{(m)}-\alpha_{m+k}\right\rceil.
\]

Since the excess doubles, the integer

\[
 \epsilon_{m,k}=2c_{k-1}-c_k\in\{0,1\}.               \tag{15}
\]

It equals one precisely when the nonzero fractional part of
`2^(k-1) Delta_m` lies in `(0,1/2]`.  Equivalently, it is determined by
the exact phase

\[
 \left\{\Phi_{m+k-1}^{(m)}-\alpha_{m+k-1}\right\},
\]

where `alpha_(m+k-1)` is one of the six rational phases of denominator
`21`.  Using the two recurrences in Section 3 gives

\[
 \boxed{
 \mathcal H_{m,k}-\mathcal H_{m,k-1}
 =2p_{m+k}^{(m)}+s_{m+k}^{(m)}+\epsilon_{m,k}
  -\bigl(q_{m+k-1}^{(m)}+W_{m+k-1}
         +t_{m+k}+1\bigr).}                           \tag{16}
\]

Thus a proper selected-divisor pulse pays twice, a half-scale pulse pays
once, and the phase half-bit pays once.  The withdrawal is the sum of the
previous quotient, the previous phase winding, the current source bit, and
one unit for the advancing horizon.

At a lower-sheet seam start, `0<Delta_m<1`, so

\[
 \mathcal H_{m,0}=F_m.
\]

Consequently the exact first-negative predicate is

\[
 \boxed{
 \mathcal H_{m,k-1}
 +2p_{m+k}^{(m)}+s_{m+k}^{(m)}+\epsilon_{m,k}
 \geq q_{m+k-1}^{(m)}+W_{m+k-1}+t_{m+k}+1.}           \tag{17}
\]

If (17) holds whenever the preceding values of `H` are nonnegative, then
`H` cannot become negative.  This is the minimal remaining one-step sign
law.  It involves the exact `1/21` phase through `W` and `epsilon`;
replacing either by a phase-free bound loses the same-cylinder distinction.

The increments in (16) are not pointwise nonnegative.  Through rank `10000`
with 64 steps from each rejected rank, there are `8925` negative increments,
`4195` of them with neither a proper-divisor nor a self-double payment.  The
most negative increment is `-16`, at `(m,k)=(6718,1)`, but it is paid from
a previous value `H=533`.  Only two audited transitions start from `H=0`;
both are nonnegative, and the smaller successor is `H=1`, at
`(m,k)=(12,2)`.  These are exact finite observations.  They show that a
proof of (17) must use stored margin: local pulse positivity is false.

The finite data suggest the following target-specific inequality.

**Phase-winding barrier.**  For the actual greedy prefix of `1/21`, if
`b_m=0`, then

\[
 \boxed{\mathcal H_{m,k}\geq0\qquad(1\leq k<m).}       \tag{18}
\]

Because `Delta_m>0`, (18) implies

\[
 F_{m+k}^{(m)}-k\geq\left\lceil2^k\Delta_m\right\rceil
 \geq1.
\]

Together with (12), this excludes every lower-sheet or upper-sliver
`0 1^k` seam of length `k<m` from producing `F_(m+k)<0`.  There is,
however, an important claim boundary.  If the actual block is `0 1^k`, then

\[
 \boxed{
 \mathcal H_{m,k}
 =F_{m+k}+1-\left\lceil2^k\Delta_m\right\rceil.}       \tag{19}
\]

Thus `H>=0` is not an independent reduction of the desired sign.  When
`ceil(2^k Delta_m)=1`, it is exactly the assertion `F_(m+k)>=0`; when the
ceiling is larger, it is strictly stronger.  The new content is the winding
decomposition (10), the pulse cancellation (11), and the one-step recurrence
(16).  They identify a possible route to the sign, but they do not yet prove
it.

The accompanying exact audit checks (18) for every rejected `m<=10000` and
every

\[
 1\leq k\leq\min(64,m-1,10000-m).
\]

The minimum is zero, at `(m,k)=(6,3)`:

\[
 F_9^{(6)}-3=1=\lceil 2^3\Delta_6\rceil.
\]

In the same range the weaker clearance

\[
 F_{m+k}^{(m)}-k
\]

has minimum one.  No rejected rank crosses the dangerous threshold (13).
For comparison, every selected rank with a complete 64-step audit window
does cross that threshold within the window; the largest first-crossing lag
is `21`, first attained at rank `6619`.  This last observation is explained
asymptotically by feasibility of the forced prefix, but the uniform lag is
only finite evidence.

No proof of (18), or of the coverage law (17), is presently known.  In
particular, (11) alone does not control the endpoint winding
`q_(m+k)^(m)`, and (10) alone does not control its integer part.

## 5. Two weaker separations do not suffice

### 5.1 Binary depth versus the old reservoir

For a lower-sheet seam start put

\[
 \ell_m=\left\lceil-\log_2\Delta_m\right\rceil.
\]

Exact interval computation through rank `20000` gives

\[
 \ell_m-F_{m-1}\leq2,
\]

with equality at `m=56`, where `ell_56=6` and `F_55=4`.  This is the direct
suffix-depth/reservoir correlation.  It is not sufficient.  For

\[
 x^-=\frac1{21}-\frac1{3\,2^{63}},
\]

the common prefix through rank `60` has `F_60=5`; at the rejected rank `61`,
`ell_61=4`.  Thus the displayed depth bound holds, but the orbit takes the
block `011` and has `F_63=-1`.

The stronger potential (14) detects this counterexample.  Its protective
alternate is the word ending in `100`, for which

\[
 F_{63}^{(61)}=2,\qquad
 \left\lceil 2^2\Delta_{61}\right\rceil=1,
 \qquad
 \mathcal H_{61,2}=-1.                               \tag{20}
\]

Thus the rounded excess term is not cosmetic: it separates the prescribed
target from the same-cylinder first failure.

### 5.2 Runs which cross the half-scale boundary

For `k>=m`, the exchange charge is no longer `k+1`.  With

\[
 g_{N,d}
 =2\left\lfloor\frac{2^N}{2^d-1}\right\rfloor
  -{\bf1}_{2d>N},
\]

the exact charge at `N=m+k` is

\[
 \Gamma_{m,N}
 =g_{N,m}-\sum_{d=m+1}^N g_{N,d}>0.                  \tag{21}
\]

The strict positivity is the superincreasing coefficient inequality for
`F_N`.  For a realized block `0 1^k`,

\[
 F_N=F_N^{(m)}-\Gamma_{m,N}.
\]

Thus the correct long-run condition is `F_N^(m)>=Gamma_(m,N)`, not (18)
with `k` substituted for the exchange charge.

The most direct phase-winding strengthening,

\[
 F_N^{(m)}-\Gamma_{m,N}+1-\lceil2^k\Delta_m\rceil\geq0,
\]

is already false for the exact `1/21` prefix at `(m,k)=(6,7)`: the three
terms are respectively `16`, `13`, and `5`, giving `-1`.  This is not
a counterexample to the desired sign, because the actual run after rank
`6` has length five and does not realize the length-seven seam.  It shows
that the rounded-excess strengthening cannot simply be extended past the
half-scale boundary for arbitrary `k`.

No actual run with `k>=m` occurs through rank `10000`; the largest ratio
is `k/m=5/6`, at `m=6`.  This is again finite evidence.  An all-depth
argument must either prove that every actual seam has `k<m`, or prove the
general exchange inequality with `Gamma_(m,N)` on the subset of `k` for
which the seam interval is actually realized.

### 5.3 Common-denominator spacing

Let

\[
 L_m=\operatorname{lcm}\left(21,
       \{2^d-1:b_d=1,\ d<m\}\right).
\]

The elementary denominator argument gives only

\[
 \operatorname{dist}(\Phi_m-\alpha_m,\mathbb Z)
 \geq \frac1{L_m}
\]

when the distance is nonzero.  At rank `61`, the actual prefix through rank
`60` already gives an `L_m` of bit length `769`.  The relevant seam has
length two.  Thus the naive spacing is on the scale `2^(-769)`, while the
interval to be excluded is on the scale `2^(-2)`.  LCM spacing by itself is
in the wrong direction by hundreds of binary digits even at this early
rank.  A denominator argument could become useful only if it also linked
the effective denominator to the `F`-margin; the raw common denominator
does not do so.

## 6. Remaining scope

Equations (4), (10), and (11) identify the common mechanism exactly.  The
binary seam and the divisor pulses are respectively the fractional doubling
and integer winding of one rational orbit.  Inequality (18) asserts that the
integer `F`-clearance dominates the rounded fractional excess before a
transient overshoot can occur.

The computation does not establish (18) at all depths.  Moreover, the
exchange charge (12) has the stated form only for `k<m`; a run crossing the
half-scale boundary requires the corresponding lower-half coefficients.
Accordingly this note supplies a new potential and an exact cancellation
law, not a solution of the dense-support case.
