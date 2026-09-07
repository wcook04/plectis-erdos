# The rational overlap fibre is typically collision-dense

## Question

The positive-measure construction in
`MultiplicityTwoRationalConstruction.md` gives continuum many pairs

\[
  x=\sum b_n w_n,\qquad y=\sum b'_n w_n,\qquad x+y=\frac32,
  \qquad w_n=\frac1{2^n-1}.
\]

If one such pair had no coordinate with \(b_n=b'_n=1\), then
\(c_n=b_n+b'_n\) would be Boolean and would give the desired rational
Mersenne subseries.  The first possible shortcut was therefore to select a
generic point of the positive-measure fibre and remove only a sparse set of
double-used coordinates.

## Discriminating computation

The script
`scripts/rational_fiber_digit_correlation_audit.py` samples fair Mersenne
codings \(x\), greedily decodes \(y=3/2-x\), and retains the pairs that survive
the Mersenne tail corridor through the requested depth.  It then records the four
joint digit frequencies \(00,01,10,11\).  Source bits are generated more than
twice as deeply as the reported prefix, the omitted tail is bounded, and a
higher-precision deterministic replay checks the accepted classification and
every decoded target bit.

This is deliberately a fibre-correlation test, not another census of the
unique greedy word for \(1/2\).

## Result at depth 512

With seed `257512` and 4096 source samples, the durable run accepted 2492
prefixes.  On the final half-window (ranks 257 through 512), it found

\[
 (p_{00},p_{01},p_{10},p_{11})
 = (0.249671,0.250180,0.250651,0.249498).
\]

The qualitative result is stable under the larger exploratory run of 8000
samples:

\[
 (p_{00},p_{01},p_{10},p_{11})
 \longrightarrow (1/4,1/4,1/4,1/4).
\]

In that larger run, 4929 prefixes were accepted.  At depths
\(64,128,256,512\), the double-use rate was respectively

\[
 0.237691,\quad 0.244402,\quad 0.246936,\quad 0.248447.
\]

The final double counts had median `127`, against the independent fair-pair
prediction \(512/4=128\); the observed range was `96` through `163`, and no
accepted prefix had at most \(0.15\cdot512\) doubles.  Thus the tail is not
showing a sparse collision cloud.  It is showing a linear-density collision
set with the same first-order law as two independent fair words.

The control target \(s=E=\sum_nw_n\) behaves completely differently and
exactly: uniqueness gives \(b'_n=1-b_n\), so its joint law is
\((0,1/2,1/2,0)\).  The instrument therefore distinguishes true
anti-correlation from the observed \(3/2\) behaviour.

### The average hides a reproducible rank profile

The coordinatewise \(11\)-frequency is not flat noise around \(1/4\).  Two
independent 2500-sample cohorts gave correlations `0.452` between their
rankwise deviations after rank 32, `0.397` after rank 64, `0.362` after rank
128, and `0.339` after rank 256.  Large deviations recur with the same sign:
rank 157 has approximately `+0.068` excess double probability in both
cohorts, and rank 421 approximately `+0.058`.

Thus two statements must be kept separate:

1. the Cesàro joint law through rank \(N\) approaches the independent quarter
   law; and
2. the single-rank correlation kernel has persistent deterministic arithmetic
   modulation.

Direct comparisons with the binary digit of \(C=E-3/2\), the greedy target
bit, and the normalized greedy residual explain only weak correlations in the
exploratory data (roughly `0.05` through `0.13`).  The profile is therefore
not captured by any one of those scalar observables.  The durable script now
stores every rankwise \(11\)-frequency, a deterministic split-cohort
replication, and the largest same-sign spikes so that the analytic kernel can
be studied without rerunning or trusting this prose snapshot.

Despite those spikes, their signed sum remains small.  In the durable cohort,

\[
 S_N=\sum_{n\leq N}(p_{11,n}-1/4)
\]

equals approximately `-0.895`, `-0.750`, `-0.793`, and `-0.921` at
\(N=64,128,256,512\); its full observed range is only about `1.04`.  A separate
depth-1024 run gave `S_1024=-1.375`.  Rational target controls
\(4/3,5/3,7/4\) likewise retained order-one envelopes through rank 512.
This discriminates a Cesàro-coboundary model from independent rank noise,
which would produce a square-root-scale partial sum.  The durable receipt now
stores every partial sum, its extrema, and its dyadic block decomposition.

The phenomenon is not a universal convolution identity.  For the exact
complement resonance \(s=E\), or more generally \(s=E-\sum_{n\in F}w_n\)
with finite \(F\), a positive-measure cylinder of pairs is coordinatewise
anti-correlated and has \(S_N=-N/4+O_F(1)\).  The experiment with
\(s=E-w_2\) reproduces the exact slope `-1/4`, whereas the non-achievement
translation \(s=E-1/4\) returns to the small-envelope regime.  This resonance
boundary leads directly to the all-scale null theorem below.

## Exact deleted-coordinate correlation kernel

The rank profile has an exact convolution description.  Let \(\mu\) be the
fair coding law, which here is Lebesgue measure restricted to \(\mathcal A\)
and has total mass one.  Delete coordinate \(n\) from the coding and call the
resulting probability law \(\mu_n\).  If \(K_n\) is the density of
\(\mu_n*\mu_n\), then

\[
 \mu=\frac12(\delta_0+\delta_{w_n})*\mu_n.
\]

Writing \(h=\mu*\mu\), expansion of the two coordinate bits gives the exact
four-cell fibre masses

\[
\begin{aligned}
 m_{00,n}(s)&=\frac14K_n(s),\\
 m_{01,n}(s)=m_{10,n}(s)&=\frac14K_n(s-w_n),\\
 m_{11,n}(s)&=\frac14K_n(s-2w_n),                            \tag{8}
\end{aligned}
\]

and therefore

\[
 h(s)=\frac14\{K_n(s)+2K_n(s-w_n)+K_n(s-2w_n)\}.           \tag{9}
\]

Since \(h(3/2)>0\), the conditional double-use probability measured by the
script is exactly

\[
 \Pr(b_n=b'_n=1\mid x+y=s)
   =\frac{K_n(s-2w_n)}{4h(s)}.                              \tag{10}
\]

For the centered coordinate signs \(r_n=2b_n-1\), the correlation is the
normalized discrete curvature

\[
 \mathbb E[r_n(x)r_n(y)\mid x+y=s]
 =\frac{K_n(s)+K_n(s-2w_n)-2K_n(s-w_n)}{4h(s)}.             \tag{11}
\]

Equations (8)--(11) explain both computational facts at once.  The persistent
single-rank spikes are samples of a deleted-coordinate convolution curvature,
while the aggregate quarter law asks for Cesàro cancellation of those
curvatures.  No inference from a flat independent model is needed.

The Boolean point remains invisible to positive fibre measure: even if every
event in (10) has positive conditional mass, the intersection of their
complements may be a nonempty null set.  Conversely, proving almost-everywhere
Cesàro quarter density would close measure selection but would not exclude
that exceptional intersection.  The actual solve route is thus sharply
separated from the generic no-go.

## All rational zero-double fibres are null

The hereditary volume theorem turns that separation into an all-scale no-go,
without any mixing conjecture.  Suppose a zero-double pair has combined
Boolean support (J).  Strict superincrease makes (J) the unique combined
support at its sum (s).  Once (J) is fixed, orienting each selected
coordinate toward the left or right shows that the set of possible left
values is exactly the supported achievement set (mathcal A_J).

The checked hereditary measure classification gives

\[
 \operatorname{vol}(\mathcal A_J)>0
 \quad\Longleftrightarrow\quad J^c\text{ is finite},        \tag{12}
\]

with volume (2^{-|J^c|}) in the cofinite case.  But then

\[
 s=\sum_{n\in J}w_n
   =E-\sum_{n\in J^c}w_n
\]

is irrational: (E) is the irrational Erdős--Borwein Mersenne constant and
the omitted sum is finite and rational.  Consequently,

\[
 \boxed{s\in\mathbb Q\text{ and }s\in\mathcal A
   \quad\Longrightarrow\quad
   \operatorname{vol}(\mathcal A_J)=0.}                    \tag{13}
\]

This is now represented in
`MersenneSubseriesRigidity.lean` by
`volume_supportedMersenneAchievementSet_eq_zero_of_rat_value`: any normalized
Boolean support whose Mersenne value is rational has a null supported
achievement set.  Its proof reuses the existing theorem that every rational
represented value has infinitely many canonical skipped coordinates and the
hereditary zero-volume theorem for an infinite complement.

Thus no positive-measure, almost-everywhere, density-point, or random-selection
argument can directly produce a Boolean rational point from the large
multiplicity-two fibre.  A counterexample to Problem 257 must be a genuinely
exceptional null-fibre point.  Equation (13) does not exclude such a point;
it classifies exactly why measure positivity cannot find one.

## One-way mechanism decision

The computation eliminates the proposed *generic-fibre selection plus sparse
collision cleanup* mechanism.  A typical positive-measure fibre point carries
about \(N/4\) doubles through rank \(N\); cleaning it is an extensive rewrite,
not a sparse repair.  Under the matching independent model, a zero-double
prefix has probability \((3/4)^N\), so the Boolean point—if it exists—lies in
an exponentially exceptional anti-correlated part of the fibre.

This does **not** prove that no exceptional zero-double point exists.  Such a
point is exactly the unresolved Boolean representation (equivalently the hard
\(1/2\) greedy orbit after taking \(w_1=1\)).  The useful new boundary is that
measure positivity supplies multiplicity-two rational points but cannot, by
genericity alone, supply Booleanity.  Any successful continuation must create
global anti-correlation, not merely select a normal point and repair a few
collisions.

## Next analytic target

The exact kernel suggests studying the coordinate Rademacher functions
\(r_n(x)=2b_n(x)-1\) on the restricted fibre
\(A\cap(3/2-A)\).  A theorem of the form

\[
 \frac1N\sum_{n\le N} r_n(x)r_n(3/2-x)\longrightarrow0
 \quad\text{for a.e. fibre point }x
\]

would rigorously bind the observed \(1/4\) double density and permanently
close every almost-everywhere Booleanisation argument, while leaving only the
exceptional-point route that can actually solve Problem 257.

The split-cohort result sharpens the target: pointwise convergence of the
single-rank correlation to zero is not the supported model.  What is needed is
Cesàro cancellation of an arithmetically modulated correlation kernel.

## Exceptional-point update: unit seam ancestry

The reduced-denominator audit closes a tempting return to the raw remainder
coordinate.  Large selected ranks contribute private cyclotomic factors which
cannot cancel against the other summands, so quadratic denominator growth is
structural rather than an artefact of an lcm upper bound.  The exceptional
point must therefore be controlled in a quotient/defect coordinate which
retains selected-support ancestry.

`HalfSeamUnitRemainderAncestry.lean` supplies such an all-scale law for the
degenerate branch left by `FatalBorrowMidpointTransfer.lean`.  Suppose an
upper reset at row `d`, followed by `k` right steps, lands at the unit seam
remainder.  If `E` is the reset charge and `C_k` is the genuine base-four
divisor-incidence pulse packet, then Lean proves

\[
  4^k E+C_k+1=2^{d+k+1}.
\]

Under the natural late-run bound `k <= d`, this implies

\[
  4^k\mid 1+C_k,
\]

and, more strongly, every terminal suffix packet `C_{k,r}` satisfies

\[
  4^r\mid 1+C_{k,r}\qquad(0\le r\le k).                  \tag{14}
\]

The three theorems
`seamUpperThenRightRun_unit_exactCharge`,
`four_pow_dvd_one_add_rightRunCharge_of_unit`, and
`four_pow_dvd_one_add_rightRunCharge_suffix_of_unit` are kernel-checked with
only the standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

Equation (14) does not yet exclude the unit state.  Its value is that the
formerly scalar `R=0` fatal branch is now a nested selected-divisor
congruence problem at every suffix depth.  A successful exclusion can target
the actual paired incidence digits in one of these packets; it no longer has
to recover information from the enormous reduced denominator or from fibre
measure statistics.

### Four-digit discriminator and its exact countermodel

A named exact probe tested whether the first four congruences in (14) could
already be excluded from the universally forced prefix.  Along the actual
seam orbit through row 2000, no upper/right endpoint matches four nested
unit-suffix congruences; the maximum matching depth is three.  The successive
records occur at rows 8, 79, and 172.

That observation is not a universal fixed-prefix lemma.  At source row 59,
take the forced support

\[
  \{2,3,6,7,14,20,21,26\}
\]

and additionally select ranks 41 and 42.  Four formal right extensions have
the exact paired-incidence pulse word

\[
  (6,1,5,7).
\]

The affine packet recurrence `C_{j+1}=4C_j+p_j+4`, starting at zero, gives

\[
  C_4=767,\qquad 1+C_4=768=3\cdot4^4.
\]

Thus every four-digit suffix congruence is compatible with Boolean support
and the forced prefix.  The countermodel uses both ranks 41 and 42, while the
actual half-greedy delayed borrow makes the decision `(a_41,a_42)=(0,1)`.
This identifies the next proof input precisely: a unit-state exclusion must
transport actual selected/omitted ancestry into the suffix packet.  A phase
sieve which remembers only the permanently forced low ranks cannot close the
branch.

### Quotient-coordinate transport and its sharp boundary

The reduced-denominator result dictates a change of coordinate rather than a
sharper estimate in the same remainder coordinate.  Before the two-thirds
crossing, the consecutive ranks added by a right run are pulse-invisible, so
the whole pulse packet is carried by the frozen reset support.  Combining
this fact with the exact multiplicity-window identity gives the new
kernel-checked law

\[
  4^k\mid 3F+4^k-1,
  \qquad\text{equivalently}\qquad
  3F\equiv1\pmod {4^k},                                  \tag{15}
\]

where (F) is the integer numerator of the (2k)-row selected-divisor
multiplicity window beginning at binary row (2(d+1)).  This is theorem
`four_pow_dvd_three_mul_resetMultiplicityWindow_add_fourPow_sub_one_of_unit`
in `HalfSeamUnitRemainderAncestry.lean`.  It consumes the actual reset
support and contains no rational Mersenne denominator.

The centered-carry telescope rewrites (15) as

\[
  4^k\mid 3c_{\rm end}+4.                                 \tag{16}
\]

The Lean corollary
`int_four_pow_dvd_three_mul_resetCarryEnd_add_four_of_unit` records this
algebraic endpoint form.  Its focused build and final serialized authority
check both pass (3346 jobs); the five unit-ancestry theorems use only the
standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

The exact seam audit now computes both sides of (15)--(16), asserts their
residue agreement, and measures only upper/right blocks wholly before the
two-thirds crossing.  Through row 2000 there are 237 applicable blocks.
There are 29 full lattice hits even though none is a unit endpoint; the
longest full hit has (k=2) at endpoint row 490, with (F=27) and
(3F\equiv1\pmod {16}).  A (k=4) block at endpoint 1983 matches three
base-four digits before failing on the fourth.

Thus (15) is a real selected-ancestry discriminator but not a standalone
exclusion theorem.  The universal statement "the actual frozen reset support
never reaches the inverse-of-three residue" is exactly false.  The remaining
proof must retain one more scalar from the complete cylinder: the reset
charge or, equivalently, the endpoint magnitude.  A sufficient next lemma is
an Archimedean-lattice incompatibility showing that a full lattice hit cannot
simultaneously satisfy the exact unit endpoint equation.

The mature fatal-zero packet supplies two additional necessary local
conditions: its terminal pulse is exactly one and its endpoint rank is zero
modulo three.  The strengthened exact audit still has three false positives
through row 2000, at endpoints 513, 585, and 1422.  The first two have
`k = 1`, with multiplicity-window numerators 7 and 15; the third has `k = 2`
and numerator 43.  Hence even the conjunction

\[
  3F\equiv1\pmod {4^k},\qquad p_{\rm end}=1,
  \qquad d\equiv0\pmod3
\]

is not an exclusion theorem.  This exact falsifier is captured as
`cap_quick_erdos257_fatal_phase_does_not_close_unit_b105f16e0a51`.

Pulse one does, however, expose a sharper coordinate that the lattice audit
does not yet consume.  Since

\[
 p_{\rm end}
 =c_A(2d+2)+2c_A(2d+1)=1,
\]

nonnegativity forces the ordered boundary coefficients
`c_A(2d+1)=0` and `c_A(2d+2)=1`.  Transporting these two exact values through
`localPrefixQuotient_succ` gives the exact two-step law

\[
  Q_A(2d+2)=4Q_A(2d)+1.                                \tag{17}
\]

The kernel-checked theorems
`pairedSupportCoeff_eq_zero_one_of_wordPulse_eq_one` and
`localPrefixQuotient_add_two_eq_four_mul_add_one_of_wordPulse_eq_one`
formalize these statements.  Unlike another phase sieve, (17) retains the
moving selected-divisor ancestry at the two rows immediately after the fatal
midpoint.  The next consumer should combine it with the fatal packet's exact
midpoint quotient rather than return to a remainder denominator.

That combination is now also kernel-checked.  Inserting the terminal rank
does not change either boundary coefficient, so an exact midpoint row

\[
  Q_{A\cup\{d\}}(2d)=2^{2d-1}
\]

with unit pulse necessarily gives

\[
  Q_{A\cup\{d\}}(2d+2)=2^{2d+1}+1
    =\operatorname{halfEndpointTarget}(2d+2)+2.          \tag{18}
\]

This is theorem
`localPrefixQuotient_insert_terminal_add_two_eq_pow_add_one_of_midpoint_unit`.
Equation (18) is a concrete post-fatal quotient signature, not an estimate:
the hypothetical fatal row is transported exactly two units above the next
half target.  The remaining consumer problem is to connect this fixed-support
overshoot to the moving greedy decision at ranks `2d+1` and `2d+2`.

## Denominator growth redirects the zero branch into a unit phase cell

A separate exact denominator audit rules out returning to rational spacing.
For a selected `d` in the top dyadic block `(n/2,n]`, put

\[
 U_d=\frac{\Phi_d(2)}{\gcd(\Phi_d(2),d)}.
\]

After also removing primes in the fixed target denominator, this primitive
part occurs in exactly one selected Mersenne denominator.  For the half target
no further removal is needed because `U_d` is odd.  The pairwise-coprime
survivors therefore force the safe lower bound

\[
 \log_2\operatorname{den}(r_n)
 \ge \sum_{d\in A\cap(n/2,n]}
   \bigl(\varphi(d)-\log_2 d-O(1)\bigr).
\]

The measured reduced denominators lose only a negligible number of bits to
cancellation.  This is structural evidence against every attempt to exclude
the fatal window by a finer estimate of the same remainder denominator.  It
also explains why the quotient and defect producers are the live frontier:
they change coordinates before the quadratic denominator growth appears.

For the midpoint-zero branch that coordinate change is now exact.  Put
`P = halfGreedyPrefixSupport (d-1)` and `D=P∪{d}`.  A skipped rank with

\[
 Q_D(2d)=2^{2d-1}
\]

satisfies

\[
 \operatorname{localFractionMass}(D,2d)
 =4^d\bigl(w_d-r_{d-1}\bigr).                          \tag{19}
\]

If the selected-ancestry complement budget is nonpositive, then
`T_d≤r_d=r_{d-1}`.  Hence

\[
 \operatorname{localFractionMass}(D,2d)
 \le4^d(w_d-T_d)
 <4^d\bigl(w_d-\operatorname{TailLB3}(d)\bigr)<1.       \tag{20}
\]

The first equality and both inequalities are formalized in
`FatalBorrowZeroFractionalSqueeze.lean`.  The final strict unit bound is
elementary: with `t=2^d≥4`, its explicit right side is

\[
 \frac{t}{t-1}-\frac13-\frac1{7t}<1.
\]

The focused Lean target and the serialized authority build both pass.  The
axiom audit for the six declarations uses only `propext`,
`Classical.choice`, and `Quot.sound`.

Thus a fatal zero row is forced into the open unit fractional cell.  This is
strictly stronger than the earlier pulse/congruence filters and makes no use
of a reduced denominator.  Fixed-anchor residue phases do not exclude the
cell: with anchors `{2,3,6,7,14,20,21,26}`, pulse one, and `d≡0 (mod 3)`,
820 of 1076 admissible phases still lie below `2/3`.  That no-go is captured
as `cap_quick_erdos257_fixed_anchors_do_not_close_fata_0a99da931b63`.
The missing consumer is consequently precise: prove that the *moving actual
selected support* makes its row-`2d` fractional mass at least one whenever
the fatal midpoint, pulse-one, and congruence conditions hold.
