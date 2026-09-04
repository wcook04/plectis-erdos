# The (1/21) density-invariant attack

Status: theorem-discovery note, 2026-08-20. No theorem stated here is claimed
to solve Erdős 257. The reciprocal-summable case is not discussed. The object
of this note is the remaining dense-support branch at the single target
(1/21).

## Claim discipline

Three kinds of assertion occur below.

* **Lean-checked** means that the cited declaration occurs in the current
  corpus.
* **Deduction** means that a proof is given here from exact identities, but the
  result has not been added to Lean.
* **Exact computation** means integer arithmetic over the stated finite range.
  It is evidence for theorem selection, not an infinite proof.

The investigation has a negative conclusion and a positive one. The negative
conclusion is rigorous: the period-six target digits cannot, by themselves,
force a later skip after the orbit has entered a sufficiently deep
supercapacity state. There is an explicit forward-invariant all-take cone.
Consequently a successful density proof has to prevent the first sparse
saturated crossing; it cannot repair the orbit afterwards. The positive
conclusion is a sharply isolated candidate: no exact Boolean quotient row
tested through the stated range realizes the two consecutive pulse conditions
required at that crossing. Small-modulus explanations of this fact all fail.

## 1. The exact quotient orbit

For (R\geq 2), put

\[
 Q_R=\left\lfloor\frac{2^{2R}}{21}\right\rfloor,
 \qquad
 q_R(d)=\left\lfloor\frac{2^{2R}}{2^d-1}\right\rfloor.
\]

The canonical lower quotient support and its scalar remainder are

\[
 D_R=\texttt{twentyOneEvenQuotientGreedySupport}(R),\qquad
 s_R=\texttt{twentyOneEvenQuotientGreedyRemainder}(R).
\]

These are definitions at
[TwentyOneQuotientGreedy.lean:32-42](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean).
The exact row identity

\[
 \sum_{d\in D_R}q_R(d)+s_R=Q_R
\]

is `localPrefixQuotient_twentyOneEvenQuotientGreedySupport_add_remainder`
([line 4775](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean)).

Define the support and target pulses

\[
 p_R=2\#\{d\in D_R:d\mid 2R+1\}
       +\#\{d\in D_R:d\mid 2R+2\},
 \qquad
 t_R=\frac{4(2^{2R}\bmod 21)}{21}.
\]

These are `localPrefixTwoStepPulse` and
`twentyOneTargetTwoStepPulse`
([lines 659 and 744](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean)).
The target has the exact three-cycle

\[
 t_R\in\{0,3\},\qquad t_R=3\iff R\equiv2\pmod3,
\]

by `twentyOneTargetTwoStepPulse_even_cases` and
`twentyOneTargetTwoStepPulse_even_eq_three_iff`
([lines 2325 and 2357](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean)).

For an exact boundary transition set

\[
 C_R=4s_R+t_R-p_R,
 \qquad w_{R+1}=2^{R+1}+1.
\]

The new bit is taken precisely when (w_{R+1}\leq C_R), and the new
state is

\[
 s_{R+1}=
 \begin{cases}
 C_R-w_{R+1},&w_{R+1}\leq C_R,\\
 C_R,&w_{R+1}>C_R.
 \end{cases}
\]

This is the content of `twentyOneBoundaryLowerSupport` and
`twentyOneBoundaryScalarState`
([lines 1890-1897](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean)).
There is an important qualification. For the canonical rows (D_R,s_R), the
corpus proves this recurrence from (R) to (R+1) under **consecutive full
quotient/rational alignment**, not unconditionally. The precise declarations
are
`twentyOneEvenQuotientGreedySupport_succ_eq_boundary_of_fullAlignment` and
`twentyOneEvenQuotientGreedyRemainder_succ_eq_boundary_of_fullAlignment`
([lines 4972 and 5106](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean)).
Nonmembership supplies that alignment only eventually.

The signed distance from the closed binary capacity is

\[
 m_R=2^R-s_R.
\]

On a take and a skip respectively, its exact laws are

\[
 \begin{aligned}
 m_{R+1}&=4m_R+p_R+1-t_R, &&\text{take},\\
 m_{R+1}&=4m_R-2^{R+1}+p_R-t_R, &&\text{skip}.
 \end{aligned}
\]

These are Lean-checked as
`twentyOneSignedClosedMargin_boundary_of_take` and
`twentyOneSignedClosedMargin_boundary_of_skip`
([lines 1907 and 1943](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean)).

## 2. The odd-depth suffix recurrence

The binary expansion of (1/21) is purely periodic:

\[
 \frac1{21}=0.\overline{000011}_2.
\]

Let (a_n\in\{0,1\}) be its (n)-th binary digit. Thus
(a_n=1) exactly when (n\bmod6\in\{5,0\}). In the odd-depth quotient
recut, let (P_k\subseteq\{2,\ldots,k+1\}) be the fixed lower support and
let (H_k\) be the (k)-bit upper suffix numeral. The seed is

\[
 P_2=\varnothing,\qquad H_2=1,
\]

and the exact row identity is

\[
 H_k=left\lfloor\frac{2^{2k+1}}{21}\right\rfloor
      -\sum_{d\in P_k}
        \left\lfloor\frac{2^{2k+1}}{2^d-1}\right\rfloor.
\]

Define

\[
 u_k=2a_{2k+2}+a_{2k+3},\qquad
 L_k=2\#\{d\in P_k:d\mid2k+2\}
      +\#\{d\in P_k:d\mid2k+3\}.
\]

Then (u_k) cycles through (2,0,1) as (k\) runs through the residue
classes (2,0,1\pmod3). The exact extension is

\[
 A_k=4H_k+u_k-L_k,
 \qquad
 b_{k+2}=\left\lfloor\frac{A_k}{2^{k+1}}\right\rfloor,
\]

\[
 H_{k+1}=A_k-b_{k+2}2^{k+1},\qquad
 P_{k+1}=P_k\cup\bigl(\{k+2\}\text{ if }b_{k+2}=1\bigr).
\]

This follows directly by applying the two-step quotient identity to every
denominator: the two new low bits of

\[
 \left\lfloor\frac{2^{M+2}}{2^d-1}\right\rfloor
\]

are (2\mathbf1_{d\mid M+1}+\mathbf1_{d\mid M+2}). It is an exact integer
recurrence as long as (0\leq A_k<2^{k+2}), which makes the extracted digit
Boolean. That range, and agreement of the extracted digits with the canonical
greedy digits, have only been checked finitely here; they are not promoted to
theorems in this note.

The two natural discrepancy coordinates are

\[
 X_k=3\operatorname{popcount}(H_k)-k
\]

and

\[
 Z_k=\#\{d\in\{2,\ldots,k+1\}:d\notin P_k\},
 \qquad Y_k=3Z_k-k.
\]

The second coordinate has the exact but tautological cocycle

\[
 Y_{k+1}-Y_k=
 \begin{cases}
 2,&b_{k+2}=0,\\
 -1,&b_{k+2}=1.
 \end{cases}
\]

Thus a uniform lower bound for (Y_k) would prove a one-third lower density
of skipped fixed digits and hence infinitely many skips. The difficulty has
not disappeared: the update of (X_k) contains the binary carry/borrow
pattern of (u_k-L_k), so it is not a local function of the Hamming weights.

## 3. Two exact deductions from the margin law

### 3.1 A strictly closed state cannot begin an all-take tail

**Deduction.** Suppose the exact boundary recurrence holds at every transition
from a rank (R_0) onward, every new bit is taken, and (m_{R_0}\geq1).
This is impossible.

Indeed (p_R\geq0) and (t_R\leq3), so the take recurrence gives

\[
 m_{R+1}\geq4m_R-2.
\]

Put (V_R=3m_R-2). If (m_R\geq1), then (V_R\geq1), and

\[
 V_{R+1}\geq4V_R.
\]

Consequently (V_{R_0+j}\geq4^jV_{R_0}). On the other hand (s_R\geq0)
implies (m_R\leq2^R), hence (V_R<3\cdot2^R). The two bounds contradict
one another for large (j).

This potential is genuine, but it controls only the closed side. It says
nothing once (m_R<0).

### 3.2 Conditional normal form for a last skip

**Deduction.** Suppose a transition whose new rank is (L) is a skip, the
exact recurrence is valid from that transition onward, and every rank larger
than (L) is taken. Then

\[
 s_L=2^L,qquad L\equiv2\pmod3,qquad p_L\leq1,
\]

and the transition from (L) to (L+1) immediately enters strict
supercapacity.

The skip condition gives (s_L\leq2^L). If the inequality were strict, the
preceding potential would rule out the all-take tail, so (m_L=0). The first
take gives

\[
 m_{L+1}=p_L+1-t_L.
\]

This cannot be positive. Hence (t_L=3), so (L\equiv2\pmod3), and
(p_L\leq2). If (p_L=2), then (m_{L+1}=0); at the following phase the
target pulse is zero, and the next take gives
(m_{L+2}=p_{L+1}+1>0), again contradicting the potential. Therefore
(p_L\leq1), and (m_{L+1}<0).

The local conclusion agrees with two stronger Lean-checked classifiers.
`twentyOneSaturatedBoundary_crosses_iff_sparsePulse` says that a saturated
row crosses exactly when (t_R=3) and (p_R\leq1)
([line 2405](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean)).
`twentyOneSaturatedBoundary_crossing_forces_ancestor_hole` then forces a
missing ancestor at (a+1) or (2(a+1)), where (R=3a+2)
([line 2448](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean)).

This deduction does **not** eliminate the fatal branch. Under
`TwentyOneFatalAlignedBranch`, the canonical boundary recurrence is known only
after some alignment rank, while the last actual skip and first crossing may
occur earlier. The deduction cannot be transported backwards across that
unproved alignment interval. The corpus already closes late failed saturated
transitions by
`twentyOneFatalAlignedBranch_eventually_saturated_socket`
([line 3397](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean));
the initial crossing is the live case.

## 4. A no-go theorem for period-only forcing

The period-six digits do not force a future skip from an arbitrary exact
state. In fact there is a robust absorbing cone.

**Deduction (supercapacity all-take cone).** Suppose (D\subseteq
\{2,\ldots,R\}), the state has

\[
 m_R\leq-(R+1),
\]

and the exact boundary transition is used. Then the next coin is necessarily
taken and

\[
 m_{R+1}\leq-(R+2).
\]

The Lean-checked estimate
`localPrefixTwoStepPulse_le_three_mul_card`
([line 666](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean))
gives (p_R\leq3|D|\leq3R). From
(s_R=2^R-m_R\geq2^R+R+1),

\[
 C_R=4s_R+t_R-p_R
 \geq 4\cdot2^R+R+4>2^{R+1}+1.
\]

Thus the boundary coin is taken. Its margin satisfies

\[
 m_{R+1}=4m_R+p_R+1-t_R
 \leq-4(R+1)+3R+1
 =-R-3.
\]

This is at most (-(R+2)), as required. Induction gives an infinite all-take
tail for every state in the cone, independently of the phase of the target
pulse.

Even the pulse-free scalar recurrence displays the obstruction. Starting at
(R=2) with (m_2=-1), taking at every step and setting (p_R=0) gives

\[
 -1,-6,-23,-91,-366,\ldots
\]

under the target-pulse pattern (3,0,0,3,\ldots). This last sequence is only
a recurrence-level countermodel, since (p_R=0) need not arise from its
claimed all-take support. The absorbing-cone proof is stronger: it allows
every Boolean support pulse satisfying the exact universal cardinality bound.

Therefore the proposed statement “the period-six digits force infinitely many
future skips” is false as a state-machine theorem. A theorem about the actual
(1/21) orbit must show that Boolean/multiplicative ancestry prevents the
first entrance into supercapacity. This is precisely where suffix capacity
and divisor pulses must be coupled.

## 5. Candidate ledger and counterexamples

All ranks and witnesses in this section were obtained by exact integer
arithmetic. The suffix orbit was run through (k=100000); the canonical
quotient recurrence was run through rank (100000). “First” means first in
that exact replay from the stated seed.

| Candidate | Result | Minimal counterexample or exact finite evidence |
|---|---|---|
| The period class (k\bmod3), equivalently (u_k\), determines the extracted bit | False | In phase (2), (k=2) gives (b_4=0), while (k=5) gives (b_7=1). In phase (1), (k=4) gives (b_6=0), while (k=7) gives (b_9=1). In phase (0), (k=3) gives (b_5=1), while (k=12) gives (b_{14}=0). |
| Every three consecutive extracted bits contain a skip | False | Ranks (7,8,9) give `111`. |
| Every six consecutive extracted bits contain a skip | False | Ranks (281,ldots,286) give `111111`. |
| Every aligned period-six block contains a skip | False | The block beginning at rank (397\equiv1\pmod6) is `111111`. |
| Every six consecutive bits contain at least two skips | False | Ranks (5,ldots,10) give `101111`. |
| Every twelve consecutive bits contain a skip | False | Ranks (689,ldots,700) are all `1`. |
| Prefix skip density is at least (1/2) | False | Among ranks (4,ldots,9), only ranks (4) and (6) are skipped. |
| (X_k=3\operatorname{popcount}(H_k)-k) is nondecreasing | False | (X_3=3), while (X_4=-1). |
| (X_k) is nondecreasing over a three-step target period | False | (X_5=10), while (X_8=7). |
| (X_k) is nondecreasing over two target periods | False | (X_5=10), while (X_{11}=7). |
| The target phase determines the sign of (X_{k+1}-X_k) | False in every phase | Phase (0): changes (-4) at (k=3) and (+2) at (k=9). Phase (1): (+11) at (k=4) and (-1) at (k=7). Phase (2): (+2) at (k=2) and (-1) at (k=5). |
| A nonzero affine congruence in (H_k,|P_k|,k), optionally also (operatorname{popcount}(H_k)), is constant modulo (2,3,7), or (21) | False for the entire tested candidate class | Exhaustive enumeration of all coefficient tuples over each residue ring found no nonzero constant affine relation on (2\leq k\leq500). |
| The canonical positive margin avoids (0\pmod3), (0\pmod7), or (0\pmod{21}) | False | (m_9=90\equiv0\pmod3); (m_{14}=10927=7\cdot1561); (m_{21}=768726=21\cdot36606). |
| A residue of (m_R) modulo (3,7), or (21), together with (R\bmod3), determines the decision | False in the tested range | By rank (100000), every residue in each modulus occurs in every phase and both decisions occur in every phase. |
| The suffix density (operatorname{popcount}(H_k)\geq\lfloor k/3\rfloor) | Survives, not proved | It holds through (k=100000). Equality occurs only at (k=4) and (k=21) in that range. The minimum of (X_k) is (-1), first at (k=4). |
| The fixed-prefix skip discrepancy (Y_k=3Z_k-k) is bounded below | Survives, not proved | Through (k=100000), (Y_k\geq2), with first minimum at (k=10). This is the observation that would directly imply infinitely many fixed-prefix skips if proved for all (k). |

The long runs are important structurally. At (100000) recurrence steps the
extracted word has (49906) ones and (50093) zeros. Its longest all-take run
has length (20), at ranks (78441,ldots,78460); its longest all-skip run has
length (16), at ranks (35337,ldots,35352). Thus the observed density is a
global discrepancy phenomenon, not a bounded-window consequence of the
six-periodic target.

## 6. Saturation equations and the failure of small moduli

A saturated sparse crossing at rank (R\equiv2\pmod3) would require an exact
Boolean row

\[
 \sum_{d\in D}q_R(d)=Q_R-2^R,
 \qquad
 2\#\{d\in D:d\mid2R+1\}
 +\#\{d\in D:d\mid2R+2\}\leq1.
 \tag{S}
\]

An exact meet-in-the-middle search over **all** (D\subseteq\{2,\ldots,R\})
found no solution of (S) for

\[
 R=2,5,8,\ldots,41.
\]

This is not evidence for a fixed congruence. Congruence impostors occur very
early even if the row is quotient-admissible and has sparse pulse. For example:

* modulo (3), at (R=8), the admissible support (D=\{8\}) has the
  required residue and pulse (0);
* modulo (7), at (R=11), the empty support has the required residue;
* modulo (21), at (R=11), (D=\{7,9,10,11\}) has the required residue
  and pulse (0);
* modulo (2^{16}), at (R=23),
  (D=\{7,14,18,21\}) has pulse (0) and
  \[
    \sum_{d\in D}q_{23}(d)
      \equiv Q_{23}-2^{23}\equiv3120\pmod{2^{16}}.
  \]

The last witness remains far from exact equality. Its purpose is to rule out
a bounded low-bit proof, not to approximate a counterexample to (S).

The corpus already exposes a still more rigid predecessor form. If a strict
closed row creates a saturated row whose next saturated transition is bad,
then `twentyOneBadSaturatedTransition_forces_sparse_twoPulse` and
`twentyOneBadSaturatedTransition_forces_margin_residue`
([lines 2519 and 2592](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean))
give, for the predecessor rank (R\equiv1\pmod3),

\[
 4(2^R-s)+p_R=2^{R+1},\qquad 4\mid p_R,qquad p_{R+1}\leq1.
 \tag{B}
\]

Combining (B) with the exact row identity eliminates (s):

\[
 \sum_{d\in D}\bigl(4q_R(d)+
   2\mathbf1_{d\mid2R+1}+\mathbf1_{d\mid2R+2}\bigr)
 =4Q_R-2^{R+1},
 \tag{B'}
\]

while the same (D) must contribute at most one unit at the next endpoint
pair. An exact meet-in-the-middle search found no Boolean support satisfying
(B'), the next-pulse bound, (0\leq s<2^R), and (|D|\leq s), for

\[
 R=4,7,10,\ldots,40.
\]

Again a bounded dyadic congruence is not the explanation. Modulo (2^{18}),
the obstruction has already disappeared at (R=28). One congruence witness
with next pulse zero is

\[
 D=\{7,8,13,14,17,18,21,24,25,26,27,28\}.
\]

Thus any proof of the exact nonexistence suggested by the data must use an
unbounded part of the binary suffix, or an ancestry constraint that couples
many scales. Modulo (3), (7), (21), parity blocks, and every fixed number
of low binary digits are too coarse.

## 7. Best surviving law and exact remaining mismatch

The best proved law from this attack is the pair of one-sided potentials:

1. (V_R=3m_R-2) expands by at least a factor of four on an all-take tail
   that begins strictly closed, so such a tail is impossible.
2. The cone (m_R\leq-(R+1)) is forward invariant and all-take, so no target
   phase can recover the orbit after a sufficiently deep escape.

Together they show that the common wall is an entrance problem. The orbit
cannot remain forever on the positive side while taking, and it cannot return
from the deep negative side. The only passage is the constant-width saturated
socket (m_R=0), (R\equiv2\pmod3), (p_R\leq1). At that socket the binary
capacity and the divisor/LCM pulse meet exactly.

The strongest surviving unproved arithmetic statement is therefore not a
generic density slogan. It is the following Boolean quotient-row exclusion:

> No exact denominator-(21) Boolean quotient row can realize the sparse
> saturated socket (S), or, more locally, the two-pulse predecessor socket
> (B').

The computations support this statement, while the congruence witnesses show
what a proof cannot be. Its logical reach must still be handled carefully.
For the canonical fatal orbit, consecutive-row recurrence is only eventually
available, so a row-exclusion theorem has to be stated at an interface that
actually covers the first crossing. A theorem about late aligned rows alone
would merely reprove the already closed saturated-socket branch.

## 8. Next smallest decisive experiment

The next experiment should be a **backward forced-suffix enumeration**, not a
longer forward replay.

For symbolic (R=3a+1), impose (B') and (p_{R+1}\leq1). Reveal the support
digits in increasing order of the valuations

\[
 v_2(q_R(d))=2R\bmod d.
\]

At binary precision (B), only those (d) with (2R\bmod d<B) affect the
suffix equation. Record which digits are forced, then intersect them with the
divisor exclusions imposed by the sparse next pulse at
(2R+3,2R+4). Increase (B) until one of two events occurs:

1. a forced selected digit divides the next endpoint pair, giving the desired
   contradiction; or
2. a compatible family survives with (B) growing proportionally to (R),
   showing that row arithmetic alone is insufficient and that the earlier
   greedy ancestry must be added.

The present fixed-modulus witnesses predict that (B) must grow with (R).
That is precisely why this experiment can discover a scalable suffix/divisor
law, whereas checking the same orbit to a larger numerical cutoff cannot.

## 9. Reproducibility summary

The exact forward certificate command used for the independent canonical
check was

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_twenty_one_greedy.py \
  --ranks 20000 --correction-depth 2000
```

It reported (10006) selected and (9994) skipped digits, maximum selected
and skipped run length (13), no saturated quotient state, and minimum closed
capacity margin (1) at rank (6). The (100000)-step suffix, residue, and
meet-in-the-middle calculations in this note used the displayed integer
recurrences directly. No floating-point comparison was used.

The result of the attack is therefore a constrained no-go and a precise
arithmetic target, not a proof of membership: period-six density cannot force
skips after supercapacity escape; the remaining task is to prove that Boolean
divisor ancestry forbids the single sparse saturated entrance through which
that escape begins.
