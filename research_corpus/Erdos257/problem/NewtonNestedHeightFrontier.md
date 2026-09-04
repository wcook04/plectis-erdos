# Nested height and the three-state boundary

Status: exact algebra, exact rational countermodels, and finite conjecture
discrimination, 2026-08-22.  This note does **not** claim a proof of Erdős
problem 257.

## 1. The computation was used as a theorem selector

Two supplied arguments reduce a negative answer to Erdős 257 to a tempered
Boolean carry, but neither supplies the all-depth boundary theorem.  The
`1/2` quotient-row attachment correctly repairs the midpoint equality; its
unproved input is the strict-core bound.  The independent `1/21` programme
has Lean-checked consumers from subexponential Lambert defect to an infinite
rational Mersenne subseries; its unproved input is a producer preventing the
positive homogeneous escape mode.

The experiments below were designed to do three things that a longer prefix
alone cannot do:

1. compress the observed `1/21` service law into a more natural two-scale
   inequality;
2. falsify its tempting decompositions and expose survivor-selection bias;
3. test a constant-width fringe candidate which, if proved, reduces the
   `1/2` strict-core theorem to three literal states.

The companion executable is
`scripts/newton_nested_height_lab.py`.

## 2. The nested-height identity

Let

\[
 f(n)=\sum_{a\mid n}b_a,
 \qquad Q_n=2Q_{n-1}+t_n-f(n),
 \qquad H(d)=1+\max_{0\le k<d}Q_k.
\]

Suppose `2d-1` is a strict defect record.  Write

\[
 R=Q_{2d-1},\qquad g_d=f(2d)-f(d).
\]

The earlier midpoint computation proved the exact identity

\[
 g_d+Q_{2d}
 =2(R-Q_{d-1})+Q_d+t_{2d}-t_d.                  \tag{1}
\]

The new experiment found that the coupled service is controlled not merely
by two copies of the half-height, but by the heights at two nested scales:

\[
 \boxed{
 g_d+Q_{2d}\le H(d)+H(d/2)+t_{2d}-t_d.
 }                                                \tag{NH}
\]

Here `(NH)` is proposed only when `d` is even, `H(d)>=4`, and the row is on
the exact greedy-survivor boundary.  In the phase-matched form it is

\[
 \boxed{
 2(R-Q_{d-1})+Q_d\le H(d)+H(d/2).
 }                                                \tag{NH'}
\]

Since `H` is nondecreasing,

\[
 H(d/2)\le H(d),
\]

so `(NH)` immediately implies the even-midpoint service law

\[
 g_d+Q_{2d}\le2H(d)+t_{2d}-t_d.                 \tag{EMS}
\]

That law already implies

\[
 Q_{2d-1}+1\le2H(d),
\]

which is exactly the doubling running-maximum inequality at this plateau.
Together with the open quarter-phase record lock `(FAPL4)`, which puts every
relevant record successor into the even-midpoint regime, the theorem chain is

\[
 (NH)+(FAPL4)\Longrightarrow(EMS)\Longrightarrow(DRMH)
 \Longrightarrow Q_N=O(N)
 \Longrightarrow \frac1{21}\in\mathcal A.
\]

The checked finite-support exclusion then forces the support to be infinite
and gives a negative answer to Erdős 257.  Every consumer after `(EMS)` is
already available; `(NH)` and `(FAPL4)` are the two open producers.

## 3. Why the coupling is real

Put

\[
 \Delta_d=R-Q_{d-1}.
\]

There are two irresistible-looking ways to split `(NH')`:

\[
 \Delta_d\le H(d/2),                              \tag{S1}
\]

and

\[
 \Delta_d+Q_d\le H(d).                            \tag{S2}
\]

Adding `(S1)` and `(S2)` gives `(NH')`.  Both splits survive the first census
of 4,669 even, phase-matched, height-at-least-four record rows.  Both are
false.

The larger exact directed-interval census uses all 49,077 reduced targets
with denominator at most 401 through rank 2000.  Among its 24,509 certified
survivors it finds 92,418 selected record rows.  The results are:

| candidate | violations | minimum margin |
|---|---:|---:|
| `(S1)` | 2 | -1 |
| `(S2)` | 2 | -1 |
| coupled `(NH')` | 0 | 0 |

The two `(S1)` counterexamples are `1/114` at successor `1260` and `4/243`
at successor `252`.  The two `(S2)` counterexamples are `7/288` at successor
`780` and `139/345` at successor `220`.  No row violates both pieces: the
lost unit in one scale is paid by slack at the other.  There are 72 exact
equalities in the coupled law.

This is the useful Newtonian feature of the candidate.  It is a discrete
two-scale curvature law, not two unrelated divisor-load estimates.  Any proof
which bounds the quarter-block gain and the midpoint residue independently is
aimed at statements the exact control panel has already killed.

For the packed canonical `1/21` orbit through rank 2,000,002, all applicable
rows satisfy `(NH)`.  The older service law had minimum margin one; `(NH)` is
strictly sharper and therefore more explanatory, not merely another
rephrasing of the same finite pass.

## 4. The survivor census is not allowed to impersonate a proof

The rational census retains targets certified alive through its cap.  That
conditioning is mathematically substantive.  To expose it, the new lab
constructs exact rational gap splices.

Fix a canonical prefix ending before rank `n`.  Write

\[
 T_n=\sum_{k>n}\frac1{2^k-1},\qquad
 w_n=\frac1{2^n-1}.
\]

The exact gap formula gives `T_n<w_n`.  The script uses the rational upper
bound

\[
 U_n=2^{-n}
 +\frac43\frac{2^{-2(n+1)}}{1-2^{-(n+1)}}
\]

and verifies `T_n<U_n<w_n`.  Taking the residual

\[
 r_n=\frac{U_n+w_n}{2}
\]

produces an exact rational target with the chosen canonical prefix, a skip at
rank `n`, and every later greedy bit equal to one.  No floating point enters
this construction.

For prescribed fatal ranks `40`, `80`, `140`, and `200`, the resulting
targets all violate `(NH)` after entering the terminal all-take regime.  The
violations grow exponentially because the defect has acquired a positive
homogeneous `2^n` component while the old heights still describe the
pre-gap prefix.

This countermodel has two consequences.

1. `(NH)` is not a theorem of the periodic digit recurrence, Boolean divisor
   convolution, or nonnegative carry alone.
2. Proving `(NH)` for the actual `1/21` orbit must use the exact greedy
   residual boundary, or an equivalent theorem excluding a final Mersenne
   tail gap.

This is the same logical boundary that killed the earlier affine and local
MILP completions.  The computation has not hidden it; it has localized it.

### 4a. Direct cylinder sampling makes the survivor bias sharper

The denominator census above still leaves one ambiguity: perhaps `(NH')`
looks special only because small-denominator rational targets visit a thin
and unusually regular part of the surviving state space.  The exact
problem-owned discriminator
[`nested_height_alive_cylinder_probe.py`](scripts/nested_height_alive_cylinder_probe.py)
removes that ambiguity without extending the canonical orbit horizon.

Choose an arbitrary Boolean prefix `A subset {2,...,N}` and an exact dyadic
residual

\[
 0\le r\le 2^{-N}<T_N.
\]

Then

\[
 x=\sum_{a\in A}\frac1{2^a-1}+r
\]

lies in the survival cylinder of `A`: strict superincreasingness forces the
greedy decisions through rank `N` to be exactly the prescribed word.  The
script verifies every one of those decisions again by integer
cross-multiplication, then reconstructs the target's binary digits, divisor
loads, defects, records, and heights with one exact common denominator.  No
floating point or survival filter is used.

The named receipt
[`nested_height_alive_cylinder_probe_receipt.json`](../../../../state/formal_math/erdos257_period_noncollapse/nested_height_alive_cylinder_probe_receipt.json)
uses 10,000 deterministic cylinder states through rank 80, eight support
density profiles from `1/20` to `9/10`, and four residual modes including both
cylinder endpoints.  It checks 3,351 applicable phase-matched record rows:

| check | violations | minimum margin |
|---|---:|---:|
| coupled `(NH')` | 0 | 1 |
| sharper causal `H(d)+2` service | 0 | 0 |
| exact greedy-prefix replay | 0 | -- |
| negative quotient defects | 0 | -- |

This is still finite evidence, but it is evidence over target space rather
than another long prefix of one target.  It says that the coupled law is
compatible with a much broader hypothesis than the period-six source: a
generic exact greedy survival cylinder.  Therefore a proof which begins by
assuming the row survives and then estimates only its local divisor tail is
unlikely to distinguish `1/21` from the desired conclusion.  A viable proof
of `(NH')` must inject the periodic source *before* survival is assumed, or
the route should be treated as an alive-prefix diagnostic and proof effort
returned to a noncircular boundary producer such as the half full-shell
charge.

This conclusion is deliberately one-sided.  The receipt does not prove that
every alive cylinder satisfies `(NH')`, and it does not demote the existing
Lean implication `(NH') -> 1/21 membership`.  It records the stronger
route-selection warning: finite survivor conditioning, even when sampled
directly and exactly, supplies no independent induction across a first fatal
gap.

## 5. The `1/2` midpoint producer has a three-state fringe candidate

The supplied `1/2` argument uses the adjacent target

\[
 H_{2R}=2^{2R-1}-1
\]

and runs integer quotient greedy through ranks `2,...,R-1`.  Let the
strict-core remainder be `A_R`.  The attachment asks for

\[
 A_R\le2^{R+1}.                                   \tag{2}
\]

The last strict-core coin is elementary and exact.  For `R>=4`,

\[
\begin{aligned}
 q_{2R}(R-1)
 &=\left\lfloor\frac{2^{2R}}{2^{R-1}-1}\right\rfloor\\
 &=2^{R+1}+4.                                    \tag{3}
\end{aligned}
\]

It is tempting to say that ordinary greedy always leaves a remainder below
the last processed coin.  That assertion is false for one-copy Boolean
greedy without an additional boundary or capacity hypothesis: a remainder
larger than twice the last coin can still be large after subtracting it once.
Thus

\[
 \boxed{A_R<2^{R+1}+4.}                           \tag{4}
\]

is a separate **fringe candidate**, not a consequence of (3).  Conditional
on (4), integrality makes the missing core theorem (2) equivalent to
excluding exactly

\[
 \boxed{
 A_R\notin
 \{2^{R+1}+1,\ 2^{R+1}+2,\ 2^{R+1}+3\}.
 }                                                \tag{3S}
\]

This is a useful two-step decomposition only if (4) is proved: first enter the
constant-width fringe, then exclude its three bad states.  The terminal
midpoint plus binary bank absorbs every state at or below the window,
including the formerly feared midpoint equality.

The exact scan through `R=1400` finds no failure of (4) and none of the three
states.  It also asks
whether the strict core alone exactly represents the three adjacent targets
`2^(2R-1)+j`, `j=0,1,2`; it finds no zero residue.  These are finite
discriminators, not modular proofs.  A low-bit-only proof is implausible: the
observed core remainders occupy every residue class modulo `2`, `4`, `8`, and
`16`.

## 6. The common boundary and the exact proof route

The two attacks now meet at one sentence:

> An explicit rational source cannot enter the final superincreasing gap
> compatible with its already forced lower core.

For `1/21`, that sentence can be supplied by `(NH)` at every even record
midpoint together with the weak quarter-phase lock; it kills the homogeneous
escape through `(DRMH)`.  For `1/2`, it can be supplied by the fringe bound
(4) together with the three-state exclusion `(3S)` cofinally; the repaired
terminal bank and compactness then produce the infinite rational support.

The most economical present route is therefore a boundary theorem, not a
larger census:

1. prove the exact gap-to-carry bridge at the *first* fatal skip;
2. show that for the `1/2` source it would escape the constant-width fringe
   or force one of the three states in `(3S)`, or for the `1/21` source it
   would force the first failure of `(NH)`;
3. use the source's complete arithmetic—not one endpoint digit—to rule out
   that state;
4. invoke the already checked compactness/subexponential consumer.

The fatal-gap side of steps 1 and 2 is now represented by exact executable
countermodels and identities; the implications for an arbitrary first fatal
skip are not yet proved.  Step 3 remains open.  Calling the computation a
proof would repeat the precise mistake found in the supplied midpoint
completion.

## 7. Reproduction and claim boundary

Default exact run:

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/\
  newton_nested_height_lab.py
```

The larger disconfirmation census reported above is:

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/\
  newton_nested_height_lab.py \
  --canonical-ranks 2000 \
  --census-ranks 2000 \
  --max-denominator 401 \
  --half-through 1400
```

The reduced theorem map is exact.  The all-depth boundary theorem is not
proved.  Erdős problem 257 therefore remains open in this repository.
