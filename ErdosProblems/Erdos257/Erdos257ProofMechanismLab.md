# Erdős 257 proof-mechanism lab

Date: 2026-08-22.

Status: exact computational discrimination and a proved conditional endgame.
This note does **not** claim an unconditional solution of Erdős 257.  It
identifies the exact missing producer in the supplied midpoint argument and
separates it from three attractive statements that hold on the computed
orbit but are false for locally legal prefixes.

Executable owner:

```text
scripts/erdos257_proof_mechanism_lab.py
```

## 1. The endpoint identity

Let `epsilon_1,epsilon_2,...` be a binary target word and suppose

\[
 \tau(n)=2C_{n-1}+\epsilon_n-C_n,
 \qquad
 \tau(n)=\sum_{d\mid n}b_d,
 \qquad b_d\in\{0,1\},\quad C_0=0.                 \tag{1}
\]

For a horizon `N`, put

\[
 E_N=\sum_{n=1}^N\epsilon_n2^{N-n},
 \qquad
 q_N(d)=\left\lfloor\frac{2^N}{2^d-1}\right\rfloor
       =\sum_{j=1}^{\lfloor N/d\rfloor}2^{N-jd}. \tag{2}
\]

Multiplying (1) by `2^(N-n)` and summing gives the exact endpoint equation

\[
 \boxed{\sum_{d=1}^N b_dq_N(d)=E_N-C_N.}          \tag{3}
\]

There is no approximation in (3).  It explains the whole finite geometry.
The quotient coins are strictly superincreasing, so a fixed terminal carry
has at most one Boolean prefix.  For `d>N/2`,

\[
 q_N(d)=2^{N-d},                                   \tag{4}
\]

so the upper half is an ordinary complete binary bank.  Consecutive terminal
carry values therefore differ by an ordinary binary borrow in the newest
support bits whenever they remain in the same lower-core cylinder.

The lab independently checks (3) on every enumerated state.  Through rank
300 it holds identically for both target words

```text
1/21:      overline(000011)
period 22: overline(0000100101001011000101).
```

## 2. Audit of the supplied midpoint completion

At the even horizon `N=2R`, write

\[
 H_{2R}=2^{2R-1}-1
\]

and let `A_R` be the remainder after quotient greedy through the strict core
`2,...,R-1`.  The terminal coins are

\[
 q_{2R}(R)=2^R+1,
 \qquad
 q_{2R}(R+j)=2^{R-j}\quad(1\le j\le R).           \tag{5}
\]

Thus their Boolean achievement set is exactly

\[
 [0,2^R-1]\ \cup\ [2^R+1,2^{R+1}].               \tag{6}
\]

The supplied observation about the exceptional value is correct.  If
`A_R=2^R`, selecting the whole upper bank leaves quotient defect one from
`H_(2R)`, equivalently terminal half-carry two.  That defect is harmless for
either the linear corridor or the closed-set limit.

What (5)--(6) do **not** prove is their input:

\[
 \boxed{A_R\le 2^{R+1}}.                           \tag{7}
\]

Required cofinally, (7) is the repository's still-open
`CofinalEvenHalfCutoffCoreBound`.  The slightly weaker corridor producer

\[
 A_R\le 2^{R+1}+2R-1                              \tag{8}
\]

would also suffice.  The cap-free consumer needs only

\[
 \frac{A_R}{4^R}\longrightarrow0                 \tag{9}
\]

along a cofinal sequence.  None of (7)--(9) follows from the terminal bank.
The attachment therefore completes the **consumer after (7)**, but it does
not supply the producer (7).

## 3. The conditional proof, with every implication explicit

Assume (7) for an unbounded sequence of `R`.  Repair the terminal row by
(6), using the whole bank at `A_R=2^R`.  The resulting finite support `F_R`
satisfies terminal defect

\[
 Q_{2R}(F_R)\in\{1,2\}.                            \tag{10}
\]

For the adjacent-half convention,

\[
 Q_1=1,
 \qquad
 Q_n=2Q_{n-1}-f_F(n),
 \qquad
 f_F(n)=\sum_{d\mid n}b_d.                        \tag{11}
\]

Since `0<=f_F(n)<=floor(n/2)` for supports starting at two, an exit from
`0<=Q_n<=n` is irreversible in either direction.  Consequently (10) implies

\[
 0\le Q_n(F_R)\le n\qquad(1\le n\le2R).           \tag{12}
\]

The finite Boolean prefixes satisfying (12) form a finitely branching tree.
The unbounded sequence of repaired rows gives nodes at every depth, so
König's lemma supplies an infinite branch.  Telescoping (11) yields

\[
 \frac{Q_N}{2^N}
 =\frac12-\sum_{n=2}^N\frac{f_A(n)}{2^n}
 \longrightarrow0,                               \tag{13}
\]

and nonnegative rearrangement gives

\[
 \sum_{d\in A}\frac1{2^d-1}
 =\sum_{n\ge2}\frac{f_A(n)}{2^n}
 =\frac12.                                        \tag{14}
\]

The support is infinite because a finite sum of fractions with odd
denominators cannot reduce to `1/2`.  Hence (7), (8), or (9), with its stated
cofinal quantifier, would give a negative answer to Erdős 257.

This is a complete proof **conditional on the named producer**.

## 4. Experiment A: local laws versus the terminal boundary

The exact denominator-21 replay suggested

\[
 H(2d)\le2H(d),
 \qquad
 H(d)=1+\max_{0\le k<d}C_k.                       \tag{DRMH}
\]

`DRMH` is exceptionally strong: with `H(20)=3`, dyadic chaining and
monotonicity give a global linear carry bound, hence `1/21` membership by the
existing subexponential-carry consumer.

The lab asks the adversarial question.  It imposes exactly the period-six
digits, Boolean divisor ancestry, nonnegative carry, and the pointwise ceiling

\[
 C_n\le\lfloor\sqrt n\rfloor+2,                   \tag{15}
\]

then asks for a violation.  At terminal horizon 40 it finds the exact witness

\[
 d=20,\qquad H(20)=3,\qquad H(40)=7>6.            \tag{16}
\]

The carry suffix is

```text
..., 1, 1, 1, 2, 4, 6, 7
```

and exact freezing proves that this prefix has no legal child at rank 41
under (15).  When continuation through rank 200 is imposed first, there is no
`DRMH` violation for any `d<=20`.

Conclusion: `DRMH` is not a local consequence of periodic digits, Booleanity,
and a square-root ceiling.  The observed law is a statement about the
source-reachable terminal boundary.  The dying witness is a precise
falsifier for any proof that ignores that boundary.

The same separation occurs for the observed record phase.  A locally legal
prefix has a strict carry record at rank 20, whose successor 21 is not
divisible by 20.  Therefore the empirical phase lock

\[
 n\equiv19\pmod {20}\quad\text{at every late strict record}       \tag{17}
\]

also requires the actual boundary; it is not forced by the period-six source
and divisor equations alone.

## 5. Experiment B: the terminal cylinder is a binary bank, not MILP freedom

Exact prefix-tree enumeration retains the complete support, rather than
quotienting by terminal carry.  Through rank 300:

* (3) holds for every state;
* there is at most one state per terminal carry, as strict
  superincreasingness predicts;
* for `1/21`, every allowed carry occurs from rank 7 onward;
* for the period-22 word, every allowed carry occurs from rank 11 onward;
* at rank 300 both trees contain exactly 20 states with terminal carries
  `0,...,19`;
* the `1/21` states share support coordinates `1,...,293`, while the
  period-22 states share coordinates `1,...,294`.

The different states are therefore a short binary terminal cylinder around
one forced lower core.  They are not competing global constructions.  This
agrees with the independent deep classifier already recorded in
`PeriodicSqrtCarryConstruction.md`: at rank 32,768 the variants differ only
in their last eight support bits, and the common prefix is the canonical real
greedy word.

Controls show that this is not a word-independent compactness theorem.  With
the same ceiling, the periodic word `001011` dies by rank 15, while the zero
word retains only its trivial zero state rather than filling the allowed
carry interval.  The survival cylinder is target-specific.

## 6. Experiment C: short countermodels select the fatal mode

The horizon-40 `DRMH` countermodel is killed immediately by its frozen
terminal state.  If the square-root ceiling is removed, analogous short
violations can continue only by activating the homogeneous doubling mode:
carry values grow approximately as

\[
 C_{n+1}=2C_n+O(\tau(n+1)).                        \tag{18}
\]

This identifies the exact meaning of the long-extension filter.  It is not
discovering a new local inequality; it is rejecting the positive exponential
boundary charge.  Any proof must show that the actual rational orbit has zero
coefficient on that homogeneous mode.

Equivalently, one may prove any one of the following genuine producers:

1. the half strict-core bounds (7), (8), or (9) cofinally;
2. cofinal skips, or no final infinite run of takes, in the canonical greedy
   orbit of a rational target;
3. `DRMH` for the actual `1/21` orbit;
4. shifted normalized contraction on all eligible record edges together with
   the source-specific rank-19 phase lock;
5. all-depth feasibility of one periodic carry tree under any
   `C_N=o(2^N)` ceiling.

Each item has a checked downstream consumer.  None is currently proved by
the finite computations.

## 7. The most compressed remaining theorem

Among the available routes, `DRMH` is the smallest scalar statement with an
immediate global consequence:

> **Boundary doubling theorem.** For the canonical quotient/greedy defect of
> `1/21`, `H(2d)<=2H(d)` for every `d>=1`.

The two-million-rank receipt tests 1,000,001 doubling pairs without a failure.
The full pair table reduces exactly to one check at each plateau start, only
40 checks through that horizon.  Subadditivity is false, static divisor-load
bounds are false, the rank phase is false on locally legal prefixes, and the
lab's horizon-40 witness kills boundary-free arguments.  A proof of the
boundary doubling theorem must therefore use the actual greedy residual or
an equivalent terminal sign, together with the exact symmetric map
`d -> 2d`.

That is the present lightning route: not a larger computation, but a proof
that the positive homogeneous boundary charge cannot coexist with the
period-six source at a doubled plateau start.  Proving that sentence in an
exact inequality would finish Erdős 257 negatively by the already checked
chain

\[
 \mathrm{DRMH}
 \Longrightarrow H(N)=O(N)
 \Longrightarrow C_N/2^N\to0
 \Longrightarrow \frac1{21}\in\mathcal A
 \Longrightarrow \text{an infinite rational Mersenne subseries}. \tag{19}
\]

### Nested-height compression of the service producer

The follow-on lab
[`NewtonNestedHeightFrontier.md`](NewtonNestedHeightFrontier.md) replaces the
two-copy service budget by the sharper two-scale candidate

\[
 f(2d)-f(d)+Q_{2d}
 \le H(d)+H(d/2)+t_{2d}-t_d.                     \tag{NH}
\]

At an even midpoint, `(NH)` implies the earlier service law by monotonicity
of `H`, hence still feeds `(DRMH)`.  The denominator-at-most-401 stress census
contains 92,418 applicable survivor rows: `(NH)` has zero violations and 72
equalities.  Its two obvious summands have two exact violations each.  Exact
rational gap splices violate `(NH)` after a fatal gap and terminal all-take
run, so this is a boundary-sensitive coupled conjecture, not a local carry
lemma.

The later record-cofiniteness reduction sharpens the role of the observed
phase.  A final skip gives a positive normalized defect amplitude; because
`f(N)<=N`, every sufficiently late rank then becomes a strict record.
Therefore `(FAPL4)` is not needed in full: any cofinal supply of non-record
ranks, for example arbitrarily late repairs

\[
 f(N)\ge Q_{N-1}+t_N,
\]

already contradicts the fatal branch.  Exact gap splices acquire a terminal
all-ranks-record suffix and lose `(FAPL4)` before they lose `(NH)`.  See
[`RecordCofinitenessBoundary.md`](RecordCofinitenessBoundary.md).

### The half strict-core producer has a three-state fringe candidate

For the independent `1/2` quotient route, the last strict-core coin is
exactly `2^(R+1)+4`; this identity is Lean-checked by
`TwentyOneQuotientGreedy.localMersenneQuotient_two_mul_pred`.  It does not,
by itself, prove a bound on the final remainder: in a one-copy greedy system,
subtracting the last coin once can leave a residual at least as large as that
coin.  The estimate

\[
 A_R<2^{R+1}+4,
\]

is therefore a separate open fringe candidate.  Conditional on it, the open
coarse core bound reduces to excluding only

\[
 A_R\in\{2^{R+1}+1,2^{R+1}+2,2^{R+1}+3\}.
\]

This would replace a large-window description by three literal terminal
states.  The exact scan through `R=1400` finds no fringe failure and no
surviving three-state obstruction, but that scan is evidence rather than
proof.  Establishing both statements at all depths is another exact form of
the same real-prefix/quotient-prefix boundary problem.

## 8. Claim boundary

The computations map the structure and eliminate false proof mechanisms;
they do not replace an all-depth quantifier.  In particular:

* the midpoint equality repair is proved;
* the midpoint core-window producer is open;
* the endpoint identity and terminal binary-cylinder classification are
  proved/exactly checked;
* `(NH)`, `DRMH`, the half fringe/three-state decomposition, the record phase,
  and the weaker cofinal non-record producer remain finite conjectures or
  reductions on the actual orbit;
* no unconditional proof of Erdős 257 is claimed here.

Reproduction:

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/\
  erdos257_proof_mechanism_lab.py \
  --max-d 20 --max-record-rank 25 --extension-depth 40 --tree-depth 40

./repo-python formal_math/erdos257_period_noncollapse/scripts/\
  erdos257_proof_mechanism_lab.py \
  --max-d 20 --max-record-rank 25 --extension-depth 200 --tree-depth 300
```
