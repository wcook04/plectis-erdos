# Erdős 257: Cross-Representation Information-Loss Map

Status: working research map. This file records exact proved interfaces and exact
failure points. It is not a proof of Erdős 257 and does not promote computations
or conditional sockets to theorems.

## Purpose

The existing corpus contains many equivalent or one-way representations of a
Boolean Mersenne subsum

\[
  x(A)=\sum_{a\in A}\frac1{2^a-1}.
\]

The present task is not to select another representation. It is to determine,
for every serious representation already developed, which part of the original
object it retains and which part it discards at the point where the proof stops.
Only after this map is complete should a new state space or invariant be proposed.

Each row must eventually answer six questions:

1. What state is retained?
2. What is the exact transport law?
3. What event would prove membership, irrationality, or a rational construction?
4. What is the fatal or blind configuration?
5. What information was discarded before that configuration appeared?
6. What fact about the original Boolean support would rule it out?

## Exact common object

For a Boolean support indicator \(b_n\), define its divisor-count sequence

\[
  c_m=\sum_{d\mid m} b_d.
\]

Then, by the geometric expansion of each Mersenne reciprocal,

\[
  \sum_n\frac{b_n}{2^n-1}=\sum_m c_m2^{-m}.
\]

This identity places all representations in one system:

\[
  \text{Boolean support}
    \xrightarrow{\;\mathbf 1 * \;}
  \text{divisor forcing}
    \xrightarrow{\;\text{radix-2 carry}\;}
  \text{binary output}.
\]

The full Boolean--Möbius carry certificate is lossless: the quotient sequence,
its Boolean Möbius transform, the carry recurrence, and the tempered boundary
condition reconstruct the support and its rational value. The information loss
occurs in the smaller projections used to prove estimates.

## Provisional comparison matrix

The entries below are anchors for the source-complete map. “Discarded” means
discarded by the projection actually used at the wall, not absent from the full
original object.

| Representation | Retained state | Exact evolution or identity | Success consumer | Fatal/blind configuration | Information discarded at the wall |
|---|---|---|---|---|---|
| Real greedy remainder | Current remainder and the next Mersenne coin | Piecewise affine take/skip update; after scaling, doubling minus a coin | Remainder tends to zero, equivalently infinitely many admissible continuations | A fatal gap produces a conserved positive tail excess and exponential scaled escape | Divisor ancestry of all prior selected ranks; the state sees only the scalar remainder |
| Binary perturbation / fixed-point picture | Boolean prefix and the second-order correction \(E(b)=\sum b_n((2^n-1)^{-1}-2^{-n})\) | Equality is equivalent, after choosing a convention at dyadic ambiguity, to \(b=\operatorname{BinaryDigits}(r-E(b))\). For \(r=1/2\), `positiveMersenneSupportValue_eq_half_iff_correction_eq_complement` packages the exact correction/complement equation | A globally consistent fixed point, or the existing unbounded `HalfPrefixForcingChain`, gives a rational Boolean subsum | Binary digit selection is discontinuous at dyadic boundaries; the perturbation uncertainty after rank \(N\) is \(O(4^{-N})\) | The scalar correction does not record which proper-divisor harmonics create a boundary crossing; the current prefix-forcing producer must certify cylinder trapping by separate data |
| Boolean--Möbius carry | Integer carry, quotient/divisor forcing, Möbius transform, rational denominator | \(U_{N+1}=2U_N-qc_{N+1}\); \(\mu*c=b\) | Positivity, divisibility, Boolean Möbius quotient, and tempered growth reconstruct a rational Boolean support | Estimates usually control the carry or the quotient, but not Booleanity and the boundary condition simultaneously | Projecting to carry size loses Boolean ancestry; projecting to the quotient/Möbius side loses the tempered terminal boundary |
| Shifted rational tail orbit | Odd-denominator residue state and selected shifted atoms | Doubling modulo the odd denominator with wrap digits; each support rank contributes a periodic atom | Under \(\sum_{a\in A}1/a<\infty\), dominated averaging yields the proved irrationality theorem | In the dense case the natural majorant is \(1/a\), whose support sum diverges, so LCM-phase averaging cannot be interchanged with the infinite support sum | Uniform tail control across the LCM horizon; each finite phase is known, but not the infinite arithmetic superposition |
| Dyadic/cylinder state | A finite binary prefix, suffix numeral, terminal carry, and sometimes a seam word | Endpoint propagation is affine, of the form \(E' = 2E-C\), with exact recutting and promotion laws | A cofinal family of terminal carries with normalized size tending to zero already proves half-membership; cross-stage coherence is not required | Eventual right-seam extension, a last non-right producer, or a crossing cylinder creates a localized one-hole/critical-band state | Earlier history and divisor ancestry are deliberately forgotten when passing to a terminal consumer; the remaining task is to produce small terminal states at unbounded depths |
| Quotient-greedy \(1/21\) state | Lower quotient support, quotient remainder/supercapacity, target periodic pulse, endpoint divisor pulse | Eventually on the fatal aligned branch: \(s_{R+1}=4s_R+t_R-p_R-(2^{R+1}+1)\) | Cofinal divergence from the exact real greedy row would prove membership; suitable subcritical rows feed the compactness consumer | Nonmembership is exactly the fatal aligned branch: finite skipped set, cofinite support, eventual alignment, and a positive homogeneous \(4^R\) escape | The local forcing determines the inhomogeneous recurrence but not its boundary amplitude. The amplitude is the actual remaining infinite greedy gap |
| One-step quotient borrow | Exact quotient row, doubled suffix reservoir, next periodic target bit, next divisor contribution | `twentyOne_qRow_cocycle` gives an exact balance; a successful borrow propagates exactness | Cofinal failed borrows produce rational prefixes converging to \(1/21\), hence membership, with no support coherence assumption | Under nonmembership every sufficiently deep exact retained-prefix row must borrow successfully | Quotient exactness alone forgets the real prefix order. Real undershoot implies borrow safety, but the converse is false; a failed borrow instead gives a genuine small real overshoot |
| Affine divisor cocycle | Endpoint divisor signal \(\Lambda_R\), periodic target/correction streams, normalized affine state | Base-4 weighted divisor signal equals the Erdős--Borwein constant; a tempered rational-anchor solution transfers irrationality to the correction | Rational weighted correction plus a tempered rational anchor would contradict irrationality | On the fatal branch the correction is eventually periodic, but the state is not tempered. Subtracting its \(L4^R\) mode makes the anchor irrational | The boundary charge has moved from the forcing to the homogeneous mode; local periodicity cannot determine it |
| Lambert signed identity | Exact Dirichlet-convolution cancellation and rational scalar | For example \(\sum_d\mu(d)/(2^d-1)=1/2\) | A positivity-preserving Booleanization would construct a rational Boolean support | Splitting signs into a Boolean support overshoots; local dyadic repair does not preserve the global Lambert denominator coordinates | Positivity and Boolean support. Exact signed cancellation retains arithmetic but not an admissible \(0/1\) source |
| Multiplicative dilation / sunflower / primitive shell | Divisor ancestry under prime dilations, primitive support bits, exact reduced-modulus information | Prime differences peel support layers; first-shell subtraction isolates primitive bits; composite dilation has an exact foreign-divisor defect | A common selected slot with both strong divisibility and a small additive future tail would create denominator pressure | Existing theorems do not synchronize the multiplicatively selected slot with a small dyadic tail; composite probes introduce foreign hits | Additive binary phase and the state into which the multiplicative pulse lands |
| Generic tail-orbit abstraction | A local affine recurrence and a finite prehistory | Balanced future pulses can preserve the same rational value and prehistory while creating arbitrarily large fresh fan-out; homogeneous \(2^N\) parasites preserve the local recurrence | Only an arithmetic restriction on admissible forcing plus a boundary condition can restore rigidity | Recurrence-only rigidity is false | Both the arithmetic source constraint and the boundary condition at infinity; this is a proved no-go for any purely local scalar-state closure |
| Scalar localisation / adelic height | A rational tail, one chosen denominator channel, and a scalar intended to clear the other channels | `scalarLocalization_complement_dvd` moves the complementary reduced denominator into the scalar coefficient; `linearDescender_eq_smul_eval` shows every rational-linear descender through scalar equality is one-dimensional | A simultaneous small real tail and large numerator divisibility can force denominator height | Localising to one odd or \(2\)-adic channel cannot erase the other denominator factors; the scalar pays for them | Independent denominator ancestry cannot descend through scalar equality alone. A non-scalar or support-aware channel is required |

## Cross-representation deductions already forced by the corpus

### 0. The fatal gap is exactly a broken binary carry seam

Write

\[
  e_n=\frac1{2^n-1}-2^{-n}.
\]

The ordinary binary identity is

\[
  2^{-m}=\sum_{n>m}2^{-n}.
\]

Therefore the strict Mersenne superincreasing gap is exactly

\[
  \frac1{2^m-1}-\sum_{n>m}\frac1{2^n-1}
  =e_m-\sum_{n>m}e_n>0.
\]

This is not just asymptotic language. `mersenneTail_lt_weight` proves the
strict inequality, while `mersenneGap_asymptotic_bound` proves that its main
term is \((2/3)4^{-m}\), with an explicit \(O(8^{-m})\) error. The fatal
window in `GreedyHoleNormalForm` is exactly the interval between the two
sides of this formerly exact binary carry. Thus a cofinite fatal support is
the Mersenne-perturbed version of the binary seam

\[
  0\,1111\ldots=1\,0000\ldots.
\]

For the half target the corpus already contains the exact fixed-point
equation. `halfCorrectionValue` is the selected perturbation, and
`halfComplementValue` is the complementary binary number;
`positiveMersenneSupportValue_eq_half_iff_correction_eq_complement` says that
their equality is precisely a value-\(1/2\) support. The
`HalfPrefixForcingChain` consumer proves equality when both values stay in
dyadic cylinders of unbounded depth. Hence the supercontractive fixed-point
picture from the attached analysis is already partly formalized; the missing
producer is exactly the cylinder-trapping/discontinuity problem.

There is also an exact multiplicative description of the same perturbation.
If \(c=\mathbf1*b\), then

\[
  E(b)=\sum_m(c_m-b_m)2^{-m}
      =\sum_m\left(\sum_{d\mid m,\ d<m}b_d\right)2^{-m}.
\]

Thus the perturbation is the binary value of the **proper-divisor ancestry
stream**. A dyadic seam crossing in the fixed-point picture and a divisor
pulse/carry event are the same event viewed before and after this identity.

### 1. Coherence is not the common missing datum

Several closedness consumers accept unrelated finite supports at cofinally many
depths. A terminal carry satisfying a shrinking normalized bound, or a quotient
defect that is \(o(2^n)\), is enough. Consequently, the failure of sequential
repair compatibility is a failure of one producer, not the universal wall.

### 2. Pulse size, capacity margin, local density, and fixed-period contraction are not universal invariants

Exact computations across rational targets give counterexamples to each scalar
version. In particular, the \(3/23\) greedy orbit has a skipped rank at \(1188\)
with a very small relative capacity margin and divisor pulse \(15\). These are
computational counterexamples to candidate laws, not theorems about all targets.

### 3. Fatal affine correction is not adaptive after alignment

On the \(1/21\) fatal aligned branch, the skipped support is finite. Hence its
divisor correction is eventually periodic. More precisely, a fixed skipped rank
\(d\) contributes a base-4 pulse whose total is exactly \((2^d-1)^{-1}\). Thus
the normalized homogeneous escape amplitude is not analogous to the remaining
greedy gap; it is that gap:

\[
  L
  =\frac1{21}-\sum_{d\in A}\frac1{2^d-1}
  =\frac{22}{21}
    +\sum_{d\in S,\ d\ge2}\frac1{2^d-1}
    -E_{\mathrm{EB}},
\]

where \(S\) is the finite skipped set and \(E_{\mathrm{EB}}=\sum_{d\ge1}(2^d-1)^{-1}\).
Fatality gives \(L>0\). Therefore an affine irrationality argument cannot close
by proving only that the correction is periodic: the irrational charge survives
as the non-tempered homogeneous boundary mode.

### 4. The exact joint pulse--capacity law is one-sided

On sufficiently late fatal \(1/21\) rows, write

\[
  e_R=s_R-2^R,
  \qquad
  p_R=\operatorname{localPrefixTwoStepPulse}(D_R,2R).
\]

The affine recurrence and strict supercapacity at the next row imply

\[
  p_R+2\le 4e_R+t_R\le4e_R+3,
  \qquad p_R\le4e_R+1.
\]

If every member of a finite \(F\subseteq D_R\) divides \(2R+2\), then
\(|F|\le p_R\), hence

\[
  |F|\le p_R\le4e_R+1.
\]

This rigorously forbids a large common-divisor family from landing in a
near-zero excess state. It does not provide the missing upper or return bound on
\(e_R\); the fatal homogeneous mode can already be exponentially large when the
LCM pulse arrives.

### 5. Borrow, local repair, suffix propagation, and fatal escape share one carry law

The recurring vocabulary is not merely analogous. After separating the
periodic target digit from the divisor coefficient, the one-step state has
the form

\[
  u_{n+1}=2u_n+a_{n+1}-c_{n+1}.
\]

The corpus realizes this same algebra in several coordinates.

- `twentyOne_qRow_cocycle` uses \(2s\) as the suffix reservoir,
  `twentyOneTargetBit` as \(a\), and the endpoint divisor contribution as
  \(c\). A successful borrow is exactly nonnegativity of the next carry.
- `localRepairInteger_eq_two_mul_suffix_add_one_sub_endpoint` is the same
  formula with target digit one. Boolean local repair is possible only after
  this signed carry is shown to be nonnegative and to fit the chosen window.
- `SelectedSuffixCylinder` propagates the common endpoint by the corresponding
  affine update \(E'=2E-C\); its branch and seam distinctions record where
  the updated carry lies relative to the next binary cell.
- Grouping two rows gives the base-four quotient recurrence and its affine
  homogeneous mode.

There is already an exact law forbidding the most naive “small reservoir plus
too-large pulse” alignment. In the \(1/21\) row,
`twentyOne_borrowContribution_le_reservoir_add_bit_of_prefix_le` proves that a
real Mersenne prefix below the target must have enough reservoir and target
bit to pay the next divisor contribution. The half local-repair theorem
`endpointDivisorContribution_le_two_mul_localBinarySuffix_add_one` is the
same positivity statement under its rational cutoff-undershoot hypothesis.

Conversely, a failed \(1/21\) borrow is not an unexplained obstruction:
`twentyOne_failedBorrow_prefix_interval` proves that it creates a genuine
real overshoot within \(O(M2^{-M})\), and cofinally many such failures imply
membership by closedness. Hence nonmembership forces eventual successful
borrowing. The live fatal branch is therefore **not** a sequence of borrow
failures. It is an indefinitely legal nonnegative carry trajectory whose
homogeneous component escapes.

This identifies the common mechanism more precisely than a statistical
anti-alignment slogan:

\[
\boxed{
  \text{periodic target digit}
  +\text{binary reservoir}
  -\text{divisor forcing}
  =\text{next carry}
}
\]

The remaining problem is a global classification of admissible trajectories
of this law, not another local proof that a negative carry is impossible.

### 6. Information loss is common, but it is not the whole wall

Two source-level facts falsify the strongest form of the “state too
compressed” diagnosis.

1. The global map \(A\leftrightarrow f_A\) is reversible by Möbius inversion,
   and a complete Boolean--Möbius carry certificate reconstructs both
   \(f_A\) and \(A\).
2. Under full \(1/21\) alignment, the canonical state \((D_R,s_R)\) retains
   the complete finite rational-greedy support through \(R\), not only its
   endpoint count. The fatal-branch theorem supplies an exact successor law
   for both components.

Lossy projections explain why pulse-only, margin-only, suffix-density, LCM,
and local-repair estimates repeatedly fail. They do not explain why the
lossless full states fail. There the obstruction is a boundary-value problem:
the forward recurrence is expanding, and finite forcing plus finite ancestry
does not determine whether the normalized homogeneous mode vanishes.

`GenericTailOrbitRigidity` makes both halves exact. A tempered boundary kills
the homogeneous parasite and recovers the canonical analytic tail, whereas
without tempering one may add a \(2^N\) mode without changing any local
recurrence. Its balanced-pulse family also proves that generic finite-state
autonomy is impossible without the special arithmetic source constraint.

Accordingly, any future joint state must do more than retain binary phase and
multiplicative ancestry. Those data are already present in the lossless
states. A decisive theorem must constrain the **global admissible boundary
mode** of the Boolean divisor-forced carry.

## Hypothesis under audit, not yet a theorem

The attachment motivating this map proposes two compatible descriptions:

1. a supercontractive binary fixed-point problem whose only instability is the
   hierarchy of dyadic discontinuity surfaces; and
2. a Dirichlet-convolution/radix-carry system in which LCM events are resonances
   among the higher binary harmonics of Mersenne reciprocals.

The corpus strongly supports the second description at the level of exact
identities. The first is quantitatively correct about prefix sensitivity away
from dyadic boundaries, but it has not yet been packaged as a global Lean
equivalence and must handle the two binary expansions of dyadic rationals.

The candidate common wall is therefore being tested in the following precise
form:

> Every projection that obtains quantitative control drops either the boundary
> condition at infinity (tempered/vanishing terminal mode) or the arithmetic
> ancestry/Booleanity of the forcing. No existing theorem simultaneously keeps
> both strongly enough to rule out or construct an eventually periodic output.

This sentence is not yet the promised new mathematics. It is the claim that the
source-complete map must either verify or falsify before a new joint state is
defined.

## Pending source-complete fragments

- `CorpusMapBinaryDynamics.md`: greedy, perturbative, cylinder, suffix, and
  terminal representations.
- `CorpusMapArithmeticDynamics.md`: Boolean--Möbius, shifted-atom, Lambert, and
  multiplicative representations.
- `CorpusMapBoundaryAndBooleanity.md`: generic no-go results, affine boundary
  modes, quotient-greedy alignment, and the exact status of the proposed common
  wall.
